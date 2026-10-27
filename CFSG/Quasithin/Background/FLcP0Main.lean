module

public import CFSG.Quasithin.Background.FLcP0Core
public import CFSG.Quasithin.Background.FLcP0Mat
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

@[expose] def parab (X : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) (i : ℕ) : Subgroup G :=
  X ⊓ ⨅ j ∈ {j : ℕ | 1 ≤ j ∧ j < n ∧ j ≠ i}, Subgroup.normalizer (W j : Set G)

theorem mem_parab {X : Subgroup G} {n i : ℕ} {W : ℕ → Subgroup G} {x : G} :
    x ∈ parab X n W i ↔
      x ∈ X ∧ ∀ j, 1 ≤ j → j < n → j ≠ i → x ∈ Subgroup.normalizer (W j : Set G) := by
  unfold parab
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j h1 h2 h3 => h j ⟨h1, h2, h3⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => h j hj.1 hj.2.1 hj.2.2⟩

theorem parab_le (X : Subgroup G) (n i : ℕ) (W : ℕ → Subgroup G) : parab X n W i ≤ X :=
  inf_le_left

theorem conj_mem_centralizer {H : Subgroup G} {p : G} (hp : p ∈ Subgroup.normalizer (H : Set G))
    {y : G} (hy : y ∈ Subgroup.centralizer (H : Set G)) :
    p * y * p⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : p⁻¹ * h * p ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (H : Set G)).inv_mem hp) h).1 hh
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hy _ hh'
  calc h * (p * y * p⁻¹) = p * ((p⁻¹ * h * p) * y) * p⁻¹ := by group
    _ = p * (y * (p⁻¹ * h * p)) * p⁻¹ := by rw [h1]
    _ = p * y * p⁻¹ * h := by group

theorem isSylowTwoOf_restrict {S P H : Subgroup G} (hS : IsSylowTwoOf S H) (hSP : S ≤ P)
    (hPH : P ≤ H) : IsSylowTwoOf S P := by
  refine ⟨hSP, hS.2.1, fun hd => hS.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex S P H hSP hPH
  have h2 : S.relIndex P ∣ S.relIndex H := h ▸ dvd_mul_right _ _
  exact dvd_trans hd h2

structure P0Setup (L S UL : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) where
  α : ↥L →* SLt n
  β : ↥UL ≃* Multiplicative (Vt n)
  three_le : 3 ≤ n
  surj : Function.Surjective α
  ker : ∀ a : ↥L, α a = 1 → (a : G) ∈ Subgroup.centralizer (UL : Set G)
  norm : ((S ⊓ L).subgroupOf L).map α = Ut n
  rel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
    Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u)
  L_le : L ≤ Subgroup.normalizer (UL : Set G)
  S_le : S ≤ Subgroup.normalizer (UL : Set G)
  S_norm : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L
  S2 : IsPGroup 2 ↥S
  K2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (UL : Set G))
  syl : IsSylowTwoOf S (L ⊔ S)
  W_le : ∀ k, 1 ≤ k → k < n → W k ≤ UL
  W_card : ∀ k, 1 ≤ k → k < n → Nat.card ↥(W k) = 2 ^ k
  W_norm : ∀ k, 1 ≤ k → k < n → S ≤ Subgroup.normalizer (W k : Set G)

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem W_mem {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (y : G) :
    y ∈ W k ↔ ∃ hy : y ∈ UL, Multiplicative.toAdd (D.β ⟨y, hy⟩) ∈ flagSpace n (ZMod 2) k :=
  flag_eq D.α D.β D.norm D.L_le D.rel (D.W_le k hk1 hkn) (D.W_card k hk1 hkn)
    (D.W_norm k hk1 hkn) y

theorem mem_normalizer_W {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (a : ↥L) :
    (a : G) ∈ Subgroup.normalizer (W k : Set G) ↔ D.α a ∈ stabilizer (flagSpace n (ZMod 2) k) :=
  mem_normalizer_iff_stab D.α D.β D.L_le D.rel (D.W_mem hk1 hkn) a

theorem S_le_parab (i : ℕ) : S ≤ parab (L ⊔ S) n W i := fun _ hs =>
  mem_parab.2 ⟨Subgroup.mem_sup_right hs, fun j h1 h2 _ => D.W_norm j h1 h2 hs⟩

theorem decomp {x : G} (hx : x ∈ L ⊔ S) :
    ∃ (l : ↥L) (c : G), c ∈ Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S) ∧ x = (l : G) * c :=
  exists_dec D.α D.β D.surj D.L_le D.S_le D.S_norm D.rel hx

theorem stab_of_decomp {x c : G} {l : ↥L} (hxl : x = (l : G) * c)
    (hc : c ∈ Subgroup.centralizer (UL : Set G)) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (hx : x ∈ Subgroup.normalizer (W j : Set G)) :
    D.α l ∈ stabilizer (flagSpace n (ZMod 2) j) := by
  rw [← D.mem_normalizer_W hj1 hjn]
  have hcN : c ∈ Subgroup.normalizer (W j : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (D.W_le j hj1 hjn)) hc)
  have hl : (l : G) = x * c⁻¹ := by rw [hxl]; group
  rw [hl]
  exact (Subgroup.normalizer (W j : Set G)).mul_mem hx
    ((Subgroup.normalizer (W j : Set G)).inv_mem hcN)

theorem fixes_of_decomp {x c : G} {l : ↥L} (hxl : x = (l : G) * c)
    (hc : c ∈ Subgroup.centralizer (UL : Set G)) (hx : x ∈ Subgroup.centralizer (W 2 : Set G))
    {v : Vt n} (hv : v ∈ flagSpace n (ZMod 2) 2) : mat (D.α l) *ᵥ v = v := by
  have hn2 : 2 < n := by have := D.three_le; omega
  set u : ↥UL := D.β.symm (Multiplicative.ofAdd v) with hu
  have hβu : Multiplicative.toAdd (D.β u) = v := by
    rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hu2 : (u : G) ∈ W 2 := by
    refine (D.W_mem (by norm_num) hn2 u).2 ⟨u.2, ?_⟩
    show Multiplicative.toAdd (D.β u) ∈ _
    rw [hβu]
    exact hv
  have h1 : (u : G) * x = x * (u : G) := Subgroup.mem_centralizer_iff.1 hx _ hu2
  have h2 : (u : G) * c = c * (u : G) := Subgroup.mem_centralizer_iff.1 hc _ u.2
  have h2' : (u : G) * c⁻¹ = c⁻¹ * (u : G) := by
    calc (u : G) * c⁻¹ = c⁻¹ * (c * (u : G)) * c⁻¹ := by group
      _ = c⁻¹ * ((u : G) * c) * c⁻¹ := by rw [h2]
      _ = c⁻¹ * (u : G) := by group
  have hl : (l : G) = x * c⁻¹ := by rw [hxl]; group
  have h3 : (u : G) * (l : G) = (l : G) * (u : G) := by
    rw [hl]
    calc (u : G) * (x * c⁻¹) = ((u : G) * x) * c⁻¹ := by group
      _ = (x * (u : G)) * c⁻¹ := by rw [h1]
      _ = x * ((u : G) * c⁻¹) := by group
      _ = x * (c⁻¹ * (u : G)) := by rw [h2']
      _ = x * c⁻¹ * (u : G) := by group
  have h4 : (u : G) = (l : G) * (u : G) * (l : G)⁻¹ := by
    calc (u : G) = (u : G) * (l : G) * (l : G)⁻¹ := by group
      _ = (l : G) * (u : G) * (l : G)⁻¹ := by rw [h3]
  have h5 := D.rel l u u h4
  rw [hβu] at h5
  exact h5.symm

theorem isPGroup_inf_centralizer [Finite G] :
    IsPGroup 2 ↥(parab (L ⊔ S) n W 1 ⊓ Subgroup.centralizer (W 2 : Set G)) := by
  obtain ⟨hK', hKn⟩ := kc_facts D.S_norm D.S2 D.L_le D.S_le D.K2
  have hn2 : 2 < n := by have := D.three_le; omega
  refine isPGroup_two_of_forall fun x hx => ?_
  have hxP := mem_parab.1 hx.1
  obtain ⟨l, c, hc, hxlc⟩ := D.decomp hxP.1
  have hg : D.α l ∈ Ut n := by
    refine mem_Ut_of_fixes (fun j hj2 hjn => ?_) (fun v hv => ?_)
    · exact D.stab_of_decomp hxlc hc.1 (by omega) hjn (hxP.2 j (by omega) hjn (by omega))
    · exact D.fixes_of_decomp hxlc hc.1 hx.2 hv
  obtain ⟨a, ha⟩ := isPGroup_Ut (by omega) ⟨D.α l, hg⟩
  have ha' : (D.α l) ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hker : ((l ^ 2 ^ a : ↥L) : G) ∈ Subgroup.centralizer (UL : Set G) := by
    apply D.ker
    rw [map_pow]
    exact ha'
  have hlpow : ((l ^ 2 ^ a : ↥L) : G) = (l : G) ^ 2 ^ a := rfl
  obtain ⟨b, hb⟩ := D.K2 ⟨(l : G) ^ 2 ^ a, by rw [← hlpow]; exact (l ^ 2 ^ a).2,
    by rw [← hlpow]; exact hker⟩
  have hb' : ((l : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  obtain ⟨c', hc', hxm⟩ := exists_pow_mul_of_normal hKn (Subgroup.mem_sup_left l.2) hc
    (2 ^ (a + b))
  have hlm : (l : G) ^ 2 ^ (a + b) = 1 := by
    rw [pow_add, pow_mul, hb']
  rw [hlm, one_mul] at hxm
  obtain ⟨d, hd⟩ := hK' ⟨c', hc'⟩
  have hd' : c' ^ 2 ^ d = 1 := by
    have := congrArg Subtype.val hd
    simpa using this
  refine ⟨a + b + d, ?_⟩
  rw [← hxlc] at hxm
  rw [pow_add, pow_mul, hxm, hd']

theorem inf_centralizer_le_pCoreOf [Finite G] :
    parab (L ⊔ S) n W 1 ⊓ Subgroup.centralizer (W 2 : Set G) ≤
      pCoreOf 2 (parab (L ⊔ S) n W 1) := by
  have hn2 : 2 < n := by have := D.three_le; omega
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ D.isPGroup_inf_centralizer
  refine le_normalizer_of_conj_mem fun p hp y hy => ?_
  refine ⟨(parab (L ⊔ S) n W 1).mul_mem ((parab (L ⊔ S) n W 1).mul_mem hp hy.1)
    ((parab (L ⊔ S) n W 1).inv_mem hp), ?_⟩
  have hpW : p ∈ Subgroup.normalizer (W 2 : Set G) := (mem_parab.1 hp).2 2 (by norm_num) hn2
    (by norm_num)
  exact conj_mem_centralizer hpW hy.2

theorem pCoreOf_le_S [Finite G] : pCoreOf 2 (parab (L ⊔ S) n W 1) ≤ S := by
  have hsyl : IsSylowTwoOf S (parab (L ⊔ S) n W 1) :=
    isSylowTwoOf_restrict D.syl (D.S_le_parab 1) (parab_le _ _ _ _)
  refine A4.le_of_normal_of_isSylowTwoOf hsyl (pCoreOf_le 2 _) ?_ (pCoreOf_isPGroup 2 _)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).2
    (le_normalizer_pCoreOf 2 _)

theorem not_parab_le_normalizer : ¬ parab (L ⊔ S) n W 1 ≤ Subgroup.normalizer (W 1 : Set G) := by
  have hn2 : 2 ≤ n := by have := D.three_le; omega
  obtain ⟨l, hl⟩ := D.surj (reflection n (ZMod 2) 1 le_rfl (by omega))
  intro hle
  have hmem : (l : G) ∈ parab (L ⊔ S) n W 1 := by
    refine mem_parab.2 ⟨Subgroup.mem_sup_left l.2, fun j hj1 hjn hj => ?_⟩
    rw [D.mem_normalizer_W hj1 hjn, hl]
    exact reflection_mem_stab hn2 hj
  have h1 := (D.mem_normalizer_W le_rfl (by omega) l).1 (hle hmem)
  rw [hl] at h1
  exact reflection_notMem_stab hn2 h1

theorem pCoreOf_le_centralizer [Finite G] :
    pCoreOf 2 (parab (L ⊔ S) n W 1) ≤ Subgroup.centralizer (W 2 : Set G) := by
  have hn2 : 2 < n := by have := D.three_le; omega
  set P := parab (L ⊔ S) n W 1 with hPdef
  set R := pCoreOf 2 P with hRdef
  have hRP : R ≤ P := pCoreOf_le 2 P
  have hR2 : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 P
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 P
  have hPW2 : P ≤ Subgroup.normalizer (W 2 : Set G) := fun x hx =>
    (mem_parab.1 hx).2 2 (by norm_num) hn2 (by norm_num)
  have hRW2 : R ≤ Subgroup.normalizer (W 2 : Set G) := hRP.trans hPW2
  let φ : ↥R →* MulAut ↥(W 2) := (W 2).normalizerMonoidHom.comp (Subgroup.inclusion hRW2)
  let _ : MulAction ↥R ↥(W 2) := MulAction.compHom ↥(W 2) φ
  have hsmul : ∀ (r : ↥R) (w : ↥(W 2)),
      ((r • w : ↥(W 2)) : G) = (r : G) * (w : G) * (r : G)⁻¹ := fun r w =>
    (W 2).normalizerMonoidHom_apply_apply_coe (Subgroup.inclusion hRW2 r) w
  have hcard := hR2.card_modEq_card_fixedPoints ↥(W 2)
  have hW4 : Nat.card ↥(W 2) = 4 := by
    rw [D.W_card 2 (by norm_num) hn2]
    norm_num
  have h1fix : (1 : ↥(W 2)) ∈ MulAction.fixedPoints ↥R ↥(W 2) := by
    rw [MulAction.mem_fixedPoints]
    intro r
    apply Subtype.ext
    rw [hsmul]
    simp
  have hpos : 0 < Nat.card ↑(MulAction.fixedPoints ↥R ↥(W 2)) := by
    have : Nonempty ↑(MulAction.fixedPoints ↥R ↥(W 2)) := ⟨⟨1, h1fix⟩⟩
    exact Nat.card_pos
  have hgt : 1 < Nat.card ↑(MulAction.fixedPoints ↥R ↥(W 2)) := by
    rw [hW4] at hcard
    unfold Nat.ModEq at hcard
    omega
  have hnt : Nontrivial ↑(MulAction.fixedPoints ↥R ↥(W 2)) := Finite.one_lt_card_iff_nontrivial.1 hgt
  obtain ⟨⟨w, hwfix⟩, hw1⟩ := exists_ne (⟨1, h1fix⟩ : ↑(MulAction.fixedPoints ↥R ↥(W 2)))
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwR : ∀ r ∈ R, r * (w : G) = (w : G) * r := by
    intro r hr
    have h := congrArg (fun z : ↥(W 2) => (z : G)) (MulAction.mem_fixedPoints.1 hwfix ⟨r, hr⟩)
    have h' : r * (w : G) * r⁻¹ = (w : G) := by
      have := hsmul ⟨r, hr⟩ w
      simpa [this] using h
    calc r * (w : G) = r * (w : G) * r⁻¹ * r := by group
      _ = (w : G) * r := by rw [h']
  set X : Subgroup G := W 2 ⊓ Subgroup.centralizer (R : Set G) with hXdef
  have hwX : (w : G) ∈ X := ⟨w.2, Subgroup.mem_centralizer_iff.2 fun r hr => hwR r hr⟩
  have hXW : X ≤ W 2 := inf_le_left
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := by
    refine le_normalizer_of_conj_mem fun p hp y hy => ?_
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hPW2 hp) y).1 hy.1, ?_⟩
    exact conj_mem_centralizer (hPR hp) hy.2
  have hXUL : X ≤ UL := hXW.trans (D.W_le 2 (by norm_num) hn2)
  have hSX : S ≤ Subgroup.normalizer (X : Set G) := (D.S_le_parab 1).trans hPX
  have hXdvd : Nat.card ↥X ∣ 4 := by
    have := Subgroup.card_dvd_of_le hXW
    rwa [hW4] at this
  have hXne : Nat.card ↥X ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    have : (w : G) ∈ (⊥ : Subgroup G) := h ▸ hwX
    exact hw1' (Subtype.ext (by simpa using this))
  have hXpos : 0 < Nat.card ↥X := Nat.card_pos
  have hXle : Nat.card ↥X ≤ 4 := Nat.le_of_dvd (by norm_num) hXdvd
  have hcases : Nat.card ↥X = 2 ∨ Nat.card ↥X = 4 := by
    generalize Nat.card ↥X = m at hXdvd hXne hXpos hXle
    interval_cases m <;> omega
  rcases hcases with h2 | h4
  ·
    exfalso
    have hX1 : X = W 1 := by
      ext y
      have e1 := flag_eq D.α D.β D.norm D.L_le D.rel (k := 1) hXUL (by rw [h2]; norm_num) hSX y
      exact e1.trans (D.W_mem le_rfl (by omega) y).symm
    apply D.not_parab_le_normalizer
    rw [← hX1]
    exact hPX
  ·
    have hXeq : X = W 2 :=
      Subgroup.eq_of_le_of_card_ge hXW (by rw [h4, hW4])
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzX : z ∈ X := hXeq ▸ hz
    exact (Subgroup.mem_centralizer_iff.1 hzX.2 r hr).symm

theorem pCoreOf_eq [Finite G] :
    pCoreOf 2 (parab (L ⊔ S) n W 1) = S ⊓ Subgroup.centralizer (W 2 : Set G) := by
  apply le_antisymm
  · exact le_inf D.pCoreOf_le_S D.pCoreOf_le_centralizer
  · exact (inf_le_inf_right _ (D.S_le_parab 1)).trans D.inf_centralizer_le_pCoreOf

theorem oTwoUpper_le [Finite G] :
    oTwoUpper (parab (L ⊔ S) n W 1) ≤ oPrimeResidualOf 3 (parab (L ⊔ S) n W 1) := by
  have hn2 : 2 < n := by have := D.three_le; omega
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  obtain ⟨hxP, hodd⟩ := hx
  have hxN : x ∈ Subgroup.normalizer (W 2 : Set G) := (mem_parab.1 hxP).2 2 (by norm_num) hn2
    (by norm_num)
  have hx24 : ∀ w : ↥(W 2), x ^ 24 * (w : G) * (x ^ 24)⁻¹ = (w : G) := by
    intro w
    let g : ↥(Subgroup.normalizer (W 2 : Set G)) := ⟨x, hxN⟩
    let π : Equiv.Perm ↥(W 2) := MulAut.toPerm _ ((W 2).normalizerMonoidHom g)
    have hπ : π ^ 24 = 1 := by
      have h1 : π ^ Nat.card (Equiv.Perm ↥(W 2)) = 1 := pow_card_eq_one'
      rw [Nat.card_perm, D.W_card 2 (by norm_num) hn2] at h1
      have e : (2 ^ 2).factorial = 24 := by decide
      rw [e] at h1
      exact h1
    have h2 : ((π ^ 24) w : ↥(W 2)) = w := by rw [hπ]; rfl
    have h3 : (π ^ 24) = MulAut.toPerm _ ((W 2).normalizerMonoidHom (g ^ 24)) := by
      rw [map_pow, map_pow]
    rw [h3] at h2
    have h4 := congrArg (fun z : ↥(W 2) => (z : G)) h2
    have h5 := (W 2).normalizerMonoidHom_apply_apply_coe (g ^ 24) w
    have h6 : (((W 2).normalizerMonoidHom (g ^ 24)) w : G) = ((MulAut.toPerm _ ((W 2).normalizerMonoidHom (g ^ 24))) w : G) := rfl
    rw [← h6, h5] at h4
    exact h4
  have hx24c : x ^ 24 ∈ Subgroup.centralizer (W 2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : x ^ 24 * z * (x ^ 24)⁻¹ = z := hx24 ⟨z, hz⟩
    calc z * x ^ 24 = (x ^ 24 * z * (x ^ 24)⁻¹) * x ^ 24 := by rw [h1]
      _ = x ^ 24 * z := by group
  have hx24P : x ^ 24 ∈ parab (L ⊔ S) n W 1 ⊓ Subgroup.centralizer (W 2 : Set G) :=
    ⟨Subgroup.pow_mem _ hxP 24, hx24c⟩
  obtain ⟨k, hk⟩ := D.isPGroup_inf_centralizer ⟨x ^ 24, hx24P⟩
  have hk' : (x ^ 24) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf x ∣ 3 * 2 ^ (k + 3) := by
    apply orderOf_dvd_of_pow_eq_one
    have e : 3 * 2 ^ (k + 3) = 24 * 2 ^ k := by ring
    rw [e, pow_mul]
    exact hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ (k + 3)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨j, hj⟩ := hodd
    omega
  have h3 : orderOf x ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · exact Subgroup.subset_closure ⟨hxP, 0, by simpa using h⟩
  · exact Subgroup.subset_closure ⟨hxP, 1, by simpa using h⟩

theorem concl [Finite G] :
    ¬ parab (L ⊔ S) n W 1 ≤ Subgroup.normalizer (W 1 : Set G) ∧
      pCoreOf 2 (parab (L ⊔ S) n W 1) = S ⊓ Subgroup.centralizer (W 2 : Set G) ∧
      oTwoUpper (parab (L ⊔ S) n W 1) ≤ oPrimeResidualOf 3 (parab (L ⊔ S) n W 1) :=
  ⟨D.not_parab_le_normalizer, D.pCoreOf_eq, D.oTwoUpper_le⟩

end P0Setup

end CFSG.Quasithin.FLc
