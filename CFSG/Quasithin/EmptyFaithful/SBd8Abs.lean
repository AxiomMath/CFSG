module

public import CFSG.Quasithin.EmptyFaithful.S153G28
public import CFSG.Quasithin.EmptyFaithful.SBc3List
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBd8

structure Insp28Data {Γ : Type} [Group Γ] [Finite Γ] (X J S₀ K : Subgroup Γ) : Prop where
  J_norm : J ≤ Subgroup.normalizer (X : Set Γ)
  J_eq : J = X ⊔ S₀
  syl : IsSylowTwoOf S₀ J
  red : pCoreOf 2 J = ⊥
  K_le : K ≤ X
  K_ne : K ≠ X
  U_le : S₀ ⊓ X ≤ K
  S₀_norm : S₀ ≤ Subgroup.normalizer (K : Set Γ)
  K_max : ∀ K' : Subgroup Γ, K ≤ K' → K' ≤ X → K' ≠ X →
    S₀ ≤ Subgroup.normalizer (K' : Set Γ) → K' ≤ K
  three_dvd : 3 ∣ Nat.card ↥K
  not_nine : ¬ 9 ∣ Nat.card ↥K
  Y_solv : Group.IsSolvable ↥(oPrimeResidualOf 3 K)
  quasi : CFSG.IsQuasisimple ↥X

section Gen

variable {A Γ : Type} [Group A] [Group Γ]

theorem mem_sup_of_le_normalizer {N H : Subgroup A} (hLE : H ≤ Subgroup.normalizer (N : Set A))
    {x : A} (hx : x ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, x = n * h := by
  have h1 := Subgroup.coe_mul_of_right_le_normalizer_left N H hLE
  have hx' : x ∈ (↑(N ⊔ H) : Set A) := hx
  rw [h1] at hx'
  obtain ⟨n, hn, h, hh, rfl⟩ := hx'
  exact ⟨n, hn, h, hh, rfl⟩

theorem mem_normalizer_inf' {X Y : Subgroup A} {g : A} (hX : g ∈ Subgroup.normalizer (X : Set A))
    (hY : g ∈ Subgroup.normalizer (Y : Set A)) : g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX h, hY h]

theorem three_dvd_card_of_ne_bot {H : Subgroup Γ} (h : oPrimeResidualOf 3 H ≠ ⊥) :
    3 ∣ Nat.card H := by
  by_contra hno
  apply h
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxH, k, hk⟩
  by_cases hk0 : k = 0
  · subst hk0
    simp only [pow_zero, orderOf_eq_one_iff] at hk
    simp [hk]
  · exfalso
    apply hno
    have h1 := Subgroup.orderOf_dvd_natCard H hxH
    rw [hk] at h1
    exact (dvd_pow_self 3 hk0).trans h1

theorem nine_dvd_card_of_le {H : Subgroup Γ} [Finite H]
    (h9 : 9 ∣ Nat.card H) : ∃ P : Subgroup Γ, P ≤ oPrimeResidualOf 3 H ∧ Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) 3 (n := 2) (by simpa using h9)
  refine ⟨P.map H.subtype, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨p.2, ?_⟩
    have h1 : orderOf p ∣ 3 ^ 2 := hP ▸ Subgroup.orderOf_dvd_natCard P hp
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    exact ⟨k, by show orderOf (p : Γ) = 3 ^ k; rw [Subgroup.orderOf_coe]; exact hk⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hP]
    norm_num


end Gen

section ARL

variable {A Γ : Type} [Group A] [Finite A] [Group Γ] [Finite Γ]

omit [Finite A] in
theorem pow_mul_mem_of_normal {N : Subgroup A} [N.Normal] {n s : A} (hn : n ∈ N) (m : ℕ) :
    ∃ n' ∈ N, (n * s) ^ m = n' * s ^ m := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨n' * (s ^ m * n * (s ^ m)⁻¹), N.mul_mem hn' (Subgroup.Normal.conj_mem ‹_› n hn _), ?_⟩
    rw [pow_succ, h]
    group

omit [Finite A] in
theorem mem_of_orderOf_three_pow {N S : Subgroup A} [N.Normal] (hNS : N ⊔ S = ⊤)
    (hS : IsPGroup 2 S) {x : A} {k : ℕ} (hx : orderOf x = 3 ^ k) : x ∈ N := by
  have hxm : x ∈ N ⊔ S := by rw [hNS]; exact Subgroup.mem_top x
  obtain ⟨n, hn, s, hs, rfl⟩ := mem_sup_of_le_normalizer (N := N) (H := S)
    (by intro g _; exact Subgroup.normalizer_eq_top_iff.2 ‹N.Normal› ▸ Subgroup.mem_top g) hxm
  obtain ⟨a, ha⟩ := hS ⟨s, hs⟩
  have hsa : s ^ 2 ^ a = 1 := congrArg Subtype.val ha
  obtain ⟨n', hn', h⟩ := pow_mul_mem_of_normal (N := N) (s := s) hn (2 ^ a)
  rw [hsa, mul_one] at h
  have hxa : (n * s) ^ 2 ^ a ∈ N := h ▸ hn'
  have hcop : Nat.Coprime (2 ^ a) (orderOf (n * s)) := by
    rw [hx]
    exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hc]
  exact N.pow_mem hxa c

theorem arl_data (ψ : A →* Γ) {L S M Y : Subgroup A} (hLS : L ⊔ S = ⊤) (hLn : L.Normal)
    (hS : IsSylowTwoOf S ⊤) (hker : ψ.ker ≤ M) (hSM : S ≤ M) (hLM : ¬ L ≤ M)
    (hmax : ∀ K : Subgroup A, Y ⊔ S ≤ K → K ≠ ⊤ → K ≤ M)
    (hY : Y = oPrimeResidualOf 3 M) (hY0 : Y.map ψ ≠ ⊥)
    (hYs : Group.IsSolvable ↥Y) (hY9 : ¬ 9 ∣ Nat.card ↥Y)
    (hq : CFSG.IsQuasisimple ↥(L.map ψ)) (hred : pCoreOf 2 ((⊤ : Subgroup A).map ψ) = ⊥) :
    Insp28Data (L.map ψ) ((⊤ : Subgroup A).map ψ) (S.map ψ) ((M ⊓ L).map ψ) := by
  have hSp : IsPGroup 2 S := hS.2.1
  have h3L : ∀ x ∈ M, ∀ k : ℕ, orderOf x = 3 ^ k → x ∈ L :=
    fun x _ k hx => mem_of_orderOf_three_pow hLS hSp hx
  have hYML : Y = oPrimeResidualOf 3 (M ⊓ L) := by
    rw [hY]
    unfold oPrimeResidualOf
    congr 1
    ext x
    constructor
    · rintro ⟨hxM, k, hk⟩
      exact ⟨⟨hxM, h3L x hxM k hk⟩, k, hk⟩
    · rintro ⟨⟨hxM, -⟩, k, hk⟩
      exact ⟨hxM, k, hk⟩
  have hYle : Y ≤ M ⊓ L := by
    rw [hYML]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hmapY : oPrimeResidualOf 3 ((M ⊓ L).map ψ) = Y.map ψ := by
    rw [hYML]
    exact (SBd3T.map_oPrimeResidualOf ψ 3 Nat.prime_three (M ⊓ L)).symm
  have hKcard3 : 3 ∣ Nat.card ((M ⊓ L).map ψ) :=
    three_dvd_card_of_ne_bot (by rw [hmapY]; exact hY0)
  have hker1 : ∀ a b : A, ψ a = ψ b → a⁻¹ * b ∈ M := fun a b hab => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel])
  have hU : S.map ψ ⊓ L.map ψ ≤ (M ⊓ L).map ψ := by
    rintro y ⟨⟨s, hs, rfl⟩, ⟨l, hl, hls⟩⟩
    have h2 := hker1 s l hls.symm
    have hlM : l ∈ M := by
      have h3 : l = s * (s⁻¹ * l) := by group
      rw [h3]
      exact M.mul_mem (hSM hs) h2
    exact ⟨l, ⟨hlM, hl⟩, hls⟩
  refine
    { J_norm := ?_, J_eq := ?_, syl := ?_, red := hred, K_le := ?_, K_ne := ?_, U_le := ?_,
      S₀_norm := ?_, K_max := ?_, three_dvd := hKcard3, not_nine := ?_, Y_solv := ?_, quasi := hq }
  · have hn : Subgroup.normalizer (L : Set A) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hLn
    have h1 := Subgroup.le_normalizer_map (H := L) ψ
    rw [hn] at h1
    exact h1
  · rw [← Subgroup.map_sup, hLS]
  · refine ⟨Subgroup.map_mono le_top, hSp.map ψ, ?_⟩
    have h1 : (S.map ψ).relIndex ((⊤ : Subgroup A).map ψ) = (S ⊔ ψ.ker).relIndex (⊤ ⊔ ψ.ker) :=
      Subgroup.relIndex_map_map ψ S ⊤
    have h2 : (S ⊔ ψ.ker).relIndex ((⊤ : Subgroup A) ⊔ ψ.ker) = (S ⊔ ψ.ker).index := by
      rw [top_sup_eq]
      exact Subgroup.relIndex_top_right _
    have h3 : (S ⊔ ψ.ker).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_left
    have h4 : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [show (S.subgroupOf (⊤ : Subgroup A)).index = S.index from
        Subgroup.relIndex_top_right S] at this
    intro h5
    apply h4
    have h6 : ((S.map ψ).subgroupOf ((⊤ : Subgroup A).map ψ)).index = (S.map ψ).relIndex ((⊤ : Subgroup A).map ψ) := rfl
    rw [h6, h1, h2] at h5
    exact h5.trans h3
  · exact Subgroup.map_mono inf_le_right
  · intro h
    apply hLM
    intro l hl
    have h1 : ψ l ∈ (M ⊓ L).map ψ := by
      rw [h]
      exact ⟨l, hl, rfl⟩
    obtain ⟨m, ⟨hmM, hmL⟩, hml⟩ := h1
    have h2 := hker1 m l hml
    have h3 : l = m * (m⁻¹ * l) := by group
    rw [h3]
    exact M.mul_mem hmM h2
  · exact hU
  · rintro _ ⟨s, hs, rfl⟩
    have h1 : s ∈ Subgroup.normalizer ((M ⊓ L : Subgroup A) : Set A) :=
      mem_normalizer_inf' (Subgroup.le_normalizer (hSM hs))
        (by rw [Subgroup.normalizer_eq_top_iff.2 hLn]; exact Subgroup.mem_top s)
    exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ h1)
  · intro K' hKK' hK'X hK'ne hK'norm
    set P : Subgroup A := (K' ⊔ S.map ψ).comap ψ with hP
    have hSP : S ≤ P := fun s hs => Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨s, hs, rfl⟩)
    have hYP : Y ≤ P := fun y hy =>
      Subgroup.mem_comap.2 (Subgroup.mem_sup_left (hKK' ⟨y, hYle hy, rfl⟩))
    have hPtop : P ≠ ⊤ := by
      intro htop
      apply hK'ne
      apply le_antisymm hK'X
      rintro _ ⟨l, hl, rfl⟩
      have hmem : ψ l ∈ K' ⊔ S.map ψ := by
        have : l ∈ P := by rw [htop]; exact Subgroup.mem_top l
        exact Subgroup.mem_comap.1 this
      obtain ⟨k, hk, s', hs', hks⟩ := mem_sup_of_le_normalizer hK'norm hmem
      have hs'L : s' ∈ L.map ψ := by
        have : s' = k⁻¹ * ψ l := by rw [hks]; group
        rw [this]
        exact (L.map ψ).mul_mem ((L.map ψ).inv_mem (hK'X hk)) ⟨l, hl, rfl⟩
      have hs'K : s' ∈ K' := hKK' (hU ⟨hs', hs'L⟩)
      rw [hks]
      exact K'.mul_mem hk hs'K
    have hPM : P ≤ M := hmax P (sup_le hYP hSP) hPtop
    rintro y hy
    obtain ⟨l, hl, rfl⟩ := hK'X hy
    have hlP : l ∈ P := Subgroup.mem_comap.2 (Subgroup.mem_sup_left hy)
    exact ⟨l, ⟨hPM hlP, hl⟩, rfl⟩
  · intro h9
    obtain ⟨P, hPle, hPc⟩ := nine_dvd_card_of_le h9
    rw [hmapY] at hPle
    have h1 : 9 ∣ Nat.card (Y.map ψ) := hPc ▸ Subgroup.card_dvd_of_le hPle
    exact hY9 (h1.trans (Subgroup.card_map_dvd Y ψ))
  · rw [hmapY]
    exact Group.isSolvable_of_surjective (f := ψ.subgroupMap Y) (MonoidHom.subgroupMap_surjective ψ Y)

theorem isSylowTwoOf_map' {X Y : Type} [Group X] [Group Y] {S K : Subgroup X}
    (hS : IsSylowTwoOf S K) (f : X →* Y) [Finite X] : IsSylowTwoOf (S.map f) (K.map f) := by
  obtain ⟨hSK, hp, hidx⟩ := hS
  refine ⟨Subgroup.map_mono hSK, ?_, fun h => hidx ?_⟩
  · exact hp.map f
  · let f' : ↥K →* ↥(K.map f) := (f.comp K.subtype).codRestrict (K.map f)
      (fun k => ⟨k, k.2, rfl⟩)
    have hf' : Function.Surjective f' := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    have he : (S.subgroupOf K).map f' = (S.map f).subgroupOf (K.map f) := by
      ext ⟨y, hy⟩
      rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨k, hk, hky⟩
        rw [Subgroup.mem_subgroupOf] at hk
        refine ⟨k, hk, ?_⟩
        exact congrArg Subtype.val hky
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hSK hs⟩, hs, rfl⟩
    have := Subgroup.index_map_dvd (S.subgroupOf K) hf'
    rw [he] at this
    exact h.trans this

theorem arl_inf (ψ : A →* Γ) {L S : Subgroup A} (hLS : L ⊔ S = ⊤) (hLn : L.Normal)
    (hS : IsSylowTwoOf S ⊤) : (S ⊓ L).map ψ = S.map ψ ⊓ L.map ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm (Subgroup.map_inf_le _ _ ψ)
  have hSL : IsSylowTwoOf (S ⊓ L) L :=
    CFSG.QuasithinUnique.Unc25Small.isSylowTwoOf_inf_of_mul hS le_top (fun h _ => by
      have hh : h ∈ L ⊔ S := by rw [hLS]; exact Subgroup.mem_top h
      obtain ⟨n, hn, s, hs, hh'⟩ := mem_sup_of_le_normalizer (N := L) (H := S)
        (fun g _ => Subgroup.normalizer_eq_top_iff.2 hLn ▸ Subgroup.mem_top g) hh
      exact ⟨n, hn, s, hs, hh'⟩)
  have h1 := isSylowTwoOf_map' hSL ψ
  have hP0 : (S ⊓ L).map ψ ≤ S.map ψ ⊓ L.map ψ := Subgroup.map_inf_le _ _ ψ
  have hP'W : S.map ψ ⊓ L.map ψ ≤ L.map ψ := inf_le_right
  have hP'2 : IsPGroup 2 ↥(S.map ψ ⊓ L.map ψ) := (hS.2.1.map ψ).to_le inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hP0 hP'W
  have hodd : ¬ 2 ∣ ((S ⊓ L).map ψ).relIndex (L.map ψ) := h1.2.2
  have hP0odd : ¬ 2 ∣ ((S ⊓ L).map ψ).relIndex (S.map ψ ⊓ L.map ψ) :=
    fun h => hodd (hmul ▸ Dvd.dvd.mul_right h _)
  obtain ⟨k, hk⟩ := hP'2.index (((S ⊓ L).map ψ).subgroupOf (S.map ψ ⊓ L.map ψ))
  have h2 : ((S ⊓ L).map ψ).relIndex (S.map ψ ⊓ L.map ψ) =
      ((((S ⊓ L).map ψ).subgroupOf (S.map ψ ⊓ L.map ψ))).index := rfl
  have hk0 : k = 0 := by
    by_contra hne
    apply hP0odd
    rw [h2, hk]
    exact dvd_pow_self 2 hne
  have : ((S ⊓ L).map ψ).relIndex (S.map ψ ⊓ L.map ψ) = 1 := by
    rw [h2, hk, hk0, pow_zero]
  exact Subgroup.relIndex_eq_one.1 this

end ARL

section Ctx

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autOn_eq_map_actionOn {U I X : Subgroup G} (hIU : I ≤ Subgroup.normalizer (U : Set G))
    (hX : X ≤ I) : autOn X U = (X.subgroupOf I).map (A4.actionOn U I hIU) := by
  ext a
  rw [mem_autOn_iff_exists]
  constructor
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hX hxX⟩, Subgroup.mem_subgroupOf.2 hxX, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hIU y.2, Subgroup.mem_subgroupOf.1 hy, rfl⟩

omit [Finite G] in
theorem isSylowTwoOf_subgroupOf_top' {X T : Subgroup G} (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (T.subgroupOf X) ⊤ := by
  refine ⟨le_top, hT.2.1.comap_subtype, ?_⟩
  have h : ((T.subgroupOf X).subgroupOf (⊤ : Subgroup X)).index = (T.subgroupOf X).index :=
    Subgroup.relIndex_top_right _
  rw [h]
  exact hT.2.2

theorem isSolvable_of_s3 {Y S R : Subgroup G} (hR : IsPGroup 2 ↥R) (hRle : R ≤ Y ⊔ S)
    {φ : ↥(Y ⊔ S) →* Equiv.Perm (Fin 3)} (hφ : φ.ker = R.subgroupOf (Y ⊔ S)) :
    Group.IsSolvable ↥(Y ⊔ S) := by
  have h2 : IsPGroup 2 ↥φ.ker := by
    rw [hφ]
    exact hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRle).symm
  have hnil := h2.isNilpotent
  have hs1 : Group.IsSolvable ↥φ.ker := inferInstance
  have hs2 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem not_nine_dvd_of_s3 {Y S R : Subgroup G} (hR : IsPGroup 2 ↥R) (hRle : R ≤ Y ⊔ S)
    {φ : ↥(Y ⊔ S) →* Equiv.Perm (Fin 3)} (hφs : Function.Surjective φ)
    (hφ : φ.ker = R.subgroupOf (Y ⊔ S)) : ¬ 9 ∣ Nat.card ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥φ.ker := by
    rw [hφ]
    exact hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRle).symm
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 h2
  have hq : Nat.card (↥(Y ⊔ S) ⧸ φ.ker) = 6 := by
    have h1 : Nat.card (↥(Y ⊔ S) ⧸ φ.ker) = Nat.card ↥φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : φ.range = ⊤ := MonoidHom.range_eq_top.2 hφs
    rw [h1, h3, Nat.card_congr (Subgroup.topEquiv (G := Equiv.Perm (Fin 3))).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hcard : Nat.card ↥(Y ⊔ S) = 6 * 2 ^ a := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hq, ha]
  intro h9
  have h10 : 9 ∣ Nat.card ↥(Y ⊔ S) :=
    h9.trans (Subgroup.card_dvd_of_le (le_sup_left : Y ≤ Y ⊔ S))
  rw [hcard] at h10
  have h11 : 3 ∣ 2 * 2 ^ a := by
    have : 6 * 2 ^ a = 3 * (2 * 2 ^ a) := by ring
    rw [this] at h10
    have h10' : 3 * 3 ∣ 3 * (2 * 2 ^ a) := by
      have h33 : (3 : ℕ) * 3 = 9 := by norm_num
      rw [h33]
      exact h10
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h10'
  have h12 : 3 ∣ 2 ^ (a + 1) := by rwa [pow_succ, mul_comm]
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h12
  omega

variable {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem insp28Data_of_ctx (c : Ctx15328 T Mc M V₁ V₂ Yp I L t) :
    Insp28Data (Star153 T I L) (Star153 T I I) (Star153 T I (Sgp153 T V₁))
      (Star153 T I (M ⊓ L)) := by
  have hF : Facts153 T M V₁ Yp I := c.facts.toFacts153
  obtain ⟨-, hred⟩ := SBc3.isTwoReduced_UI c.ctx hF
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := hred.2.1
  set ψ := A4.actionOn (UI153 T I) I hIU with hψ
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.ctx.inH.1.1
  have hLI : L ≤ I := (le_of_mem_cComp c.conc.1).trans (thompsonJ_le_self I)
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hYI : Yp ≤ I := hYL.trans hLI
  have hMLI : M ⊓ L ≤ I := inf_le_right.trans hLI
  have hMI : M ⊓ I ≤ I := inf_le_right
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans c.ctx.hyp.hyp.T_le
  have e1 : Star153 T I L = (L.subgroupOf I).map ψ := autOn_eq_map_actionOn hIU hLI
  have e2 : Star153 T I I = (⊤ : Subgroup ↥I).map ψ := by
    show autOn I (UI153 T I) = _
    rw [autOn_eq_map_actionOn hIU le_rfl, Subgroup.subgroupOf_self]
  have e3 : Star153 T I (Sgp153 T V₁) = ((Sgp153 T V₁).subgroupOf I).map ψ :=
    autOn_eq_map_actionOn hIU hSI
  have e4 : Star153 T I (M ⊓ L) = ((M.subgroupOf I ⊓ L.subgroupOf I)).map ψ := by
    show autOn (M ⊓ L) (UI153 T I) = _
    rw [autOn_eq_map_actionOn hIU hMLI]
    congr 1
  have e5 : Star153 T I Yp = (Yp.subgroupOf I).map ψ := autOn_eq_map_actionOn hIU hYI
  have hker : ψ.ker ≤ M.subgroupOf I := by
    intro a ha
    have h1 : (a : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
      (A4.actionOn_eq_one_iff hIU a).1 ha
    have h2 : (a : G) ∈ M ⊓ I := hF.cent_le ⟨a.2, h1⟩
    exact Subgroup.mem_subgroupOf.2 h2.1
  have hLS : L.subgroupOf I ⊔ (Sgp153 T V₁).subgroupOf I = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLI hSI, ← c.I_eq, Subgroup.subgroupOf_self]
  have hLn : (L.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLI).2 c.c27.normal
  have hS : IsSylowTwoOf ((Sgp153 T V₁).subgroupOf I) ⊤ := isSylowTwoOf_subgroupOf_top' hF.sylow
  have hSM' : (Sgp153 T V₁).subgroupOf I ≤ M.subgroupOf I := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSM (Subgroup.mem_subgroupOf.1 hx))
  have hLM : ¬ L.subgroupOf I ≤ M.subgroupOf I := by
    intro h
    apply c.conc.2.1
    intro l hl
    have h1 : (⟨l, hLI hl⟩ : ↥I) ∈ L.subgroupOf I := Subgroup.mem_subgroupOf.2 hl
    exact ⟨Subgroup.mem_subgroupOf.1 (h h1), hLI hl⟩
  have hmax : ∀ K : Subgroup ↥I, Yp.subgroupOf I ⊔ (Sgp153 T V₁).subgroupOf I ≤ K → K ≠ ⊤ →
      K ≤ M.subgroupOf I := by
    intro K hK hKtop
    have hYS : Yp ⊔ Sgp153 T V₁ ≤ K.map I.subtype := by
      refine sup_le ?_ ?_
      · intro y hy
        exact ⟨⟨y, hYI hy⟩, hK (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hy)), rfl⟩
      · intro y hy
        exact ⟨⟨y, hSI hy⟩, hK (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hy)), rfl⟩
    have hlt : K.map I.subtype < I := by
      refine lt_of_le_of_ne (by rintro _ ⟨k, -, rfl⟩; exact k.2) ?_
      intro h
      apply hKtop
      rw [eq_top_iff]
      intro x _
      have : (x : G) ∈ K.map I.subtype := by rw [h]; exact x.2
      obtain ⟨k, hk, hkx⟩ := this
      have : k = x := Subtype.ext hkx
      rwa [← this]
    have h1 := c.unique_max (K.map I.subtype) hYS hlt
    intro k hk
    exact Subgroup.mem_subgroupOf.2 (h1 ⟨k, hk, rfl⟩).1
  have hYdef : Yp.subgroupOf I = oPrimeResidualOf 3 (M.subgroupOf I) := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hYI,
      SBd3T.map_oPrimeResidualOf I.subtype 3 Nat.prime_three, ← Subgroup.inf_subgroupOf_right M I,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : M ⊓ I ≤ I)]
    exact c.facts.yp_eq
  have hY0 : (Yp.subgroupOf I).map ψ ≠ ⊥ := by
    rw [← e5]
    exact hF.star_ne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 ↥(R153 T V₁ Yp) := pCoreOf_isPGroup 2 _
  have hRle : R153 T V₁ Yp ≤ Yp ⊔ Sgp153 T V₁ := pCoreOf_le _ _
  obtain ⟨φ, hφs, hφ⟩ := c.facts.s3
  have hsolvYS : Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := isSolvable_of_s3 hR2 hRle hφ
  have hYs : Group.IsSolvable ↥(Yp.subgroupOf I) := by
    have h1 : Group.IsSolvable ↥Yp := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_sup_left : Yp ≤ Yp ⊔ Sgp153 T V₁))
      (Subgroup.inclusion_injective _)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYI).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYI).injective
  have hY9 : ¬ 9 ∣ Nat.card ↥(Yp.subgroupOf I) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYI).toEquiv]
    exact not_nine_dvd_of_s3 hR2 hRle hφs hφ
  have hq : CFSG.IsQuasisimple ↥((L.subgroupOf I).map ψ) := by
    rw [← e1]
    exact c.conc.2.2.2.2.1
  have hred' : pCoreOf 2 ((⊤ : Subgroup ↥I).map ψ) = ⊥ := by
    rw [← e2]
    exact Setup.pCoreOf_autOn_eq_bot hred
  have key := arl_data ψ hLS hLn hS hker hSM' hLM hmax hYdef hY0 hYs hY9 hq hred'
  rw [e1, e2, e3, e4]
  exact key

theorem star_inf_eq (c : Ctx15328 T Mc M V₁ V₂ Yp I L t) :
    Star153 T I (Sgp153 T V₁ ⊓ L) = Star153 T I (Sgp153 T V₁) ⊓ Star153 T I L := by
  have hF : Facts153 T M V₁ Yp I := c.facts.toFacts153
  obtain ⟨-, hred⟩ := SBc3.isTwoReduced_UI c.ctx hF
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := hred.2.1
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.ctx.inH.1.1
  have hLI : L ≤ I := (le_of_mem_cComp c.conc.1).trans (thompsonJ_le_self I)
  have hSLI : Sgp153 T V₁ ⊓ L ≤ I := inf_le_right.trans hLI
  have hLS : L.subgroupOf I ⊔ (Sgp153 T V₁).subgroupOf I = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLI hSI, ← c.I_eq, Subgroup.subgroupOf_self]
  have hLn : (L.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLI).2 c.c27.normal
  have hS : IsSylowTwoOf ((Sgp153 T V₁).subgroupOf I) ⊤ := isSylowTwoOf_subgroupOf_top' hF.sylow
  show autOn (Sgp153 T V₁ ⊓ L) (UI153 T I) =
    autOn (Sgp153 T V₁) (UI153 T I) ⊓ autOn L (UI153 T I)
  rw [autOn_eq_map_actionOn hIU hSLI, autOn_eq_map_actionOn hIU hSI,
    autOn_eq_map_actionOn hIU hLI]
  exact arl_inf (A4.actionOn (UI153 T I) I hIU) hLS hLn hS

end Ctx

@[expose] def Insp28Concl {Γ : Type} [Group Γ] [Finite Γ] (X J S₀ K : Subgroup Γ) : Prop :=
  ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n ↥X) ∧ IsBorelIn X K) ∨
  ((IsPSL 3 2 1 ↥X ∨ IsAlt 6 ↥X ∨ IsPSU 3 3 1 ↥X) ∧ IsMinParabolicOf X K ∧
      ∀ P : Subgroup Γ, IsMinParabolicOf X P →
        X ⊓ Subgroup.normalizer ((S₀ ⊓ X : Subgroup Γ) : Set Γ) ≤ P →
          S₀ ≤ Subgroup.normalizer (P : Set Γ)) ∨
  (Nonempty (↥J ≃* Equiv.Perm (Fin 8)) ∧ IsMinParabolicOf X K)

@[expose] def Insp28Pure : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X J S₀ K : Subgroup Γ), Insp28Data X J S₀ K →
    B56QuasisimpleList ↥X → ¬ IsAlt 7 ↥X → (¬ ∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) ↥X) →
      ¬ IsHat ↥X ↥(alternatingGroup (Fin 6)) → Insp28Concl X J S₀ K

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input28Insp_of_pure (h : Insp28Pure) : Input28Insp := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hlist h7
  have hd := insp28Data_of_ctx c
  have hc := h _ _ _ _ _ hd hlist h7 c.c27.not_SL3 c.c27.not_hatA6
  unfold Concl15328
  rw [star_inf_eq c]
  exact hc

end Final

end SBd8

end CFSG.Quasithin
