module

public import CFSG.Quasithin.H13.U3L15Gen
public import CFSG.Quasithin.H13.A6S4V2
public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.H13.A6S4L0
public import CFSG.Quasithin.H13.L32NModule
public import CFSG.Quasithin.H13.U3FrameKernel
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped commutatorElement

@[expose] def a6s3 : Perm (Fin 6) := c[0, 2, 4] * c[1, 3, 5]

@[expose] def a6n1 : Perm (Fin 6) := swap 2 3 * swap 4 5

@[expose] def a6n2 : Perm (Fin 6) := c[0, 1, 2]

@[expose] def a6gen : Fin 3 → Perm (Fin 6) := ![a6s3, a6n1, a6n2]

theorem cert_a6_s3 : Perm.sign a6s3 = 1 ∧ a6s3 ^ 3 = 1 ∧
    (∀ y : P6, InW2 y → InW2 (act4f a6s3 y)) ∧ act4f a6s3 (dv 0 1) ≠ dv 0 1 := by
  decide +kernel

theorem cert_a6_n : Perm.sign a6n1 = 1 ∧ Perm.sign a6n2 = 1 ∧
    (∀ y : P6, InW4 y → InW3 y → InW3 (act4f a6n1 y)) ∧
    (∀ y : P6, InW4 y → InW3 y → InW3 (act4f a6n2 y)) := by
  decide +kernel

theorem cert_a6_C2 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    (∀ y : P6, InW2 y → act4f σ y = y) → σ * σ = 1 := by
  decide +kernel

theorem cert_a6_V3 : ∀ y : P6, (InW4 y ∧ ¬ InW3 y) → ∃ σ ∈ DAgens,
    ([1, dv 0 1, dv 2 3, e0123, y, y * dv 0 1, y * dv 2 3, y * e0123, act4f σ y] :
      List P6).Nodup := by
  decide +kernel

theorem cert_a6_mod : ∀ σ : Perm (Fin 6), (∀ y : P6, (InW4 y ∧ InW3 y) → act4f σ y = y) →
    ∀ y : P6, InW4 y → (act4f σ y * y⁻¹ = 1 ∨ act4f σ y * y⁻¹ = e0123) := by
  decide +kernel

@[expose] def a6cycWords : List (List (Fin 3)) :=
  [[0, 2, 2, 0, 0, 1], [1, 0, 2, 0, 0], [0, 2, 0, 0], [0, 1, 2, 1, 0, 0], [0, 2, 2, 0, 0],
    [0, 2, 0, 0, 1], [0, 2, 0, 2, 1, 2], [0, 1, 2, 0, 1, 0], [1, 2, 2, 1, 2],
    [0, 0, 1, 2, 0, 1, 2], [0, 1, 0, 2, 0, 2], [0, 0, 1, 0, 2], [0, 0, 1, 2, 0, 2, 1],
    [0, 1, 2, 0, 2, 0, 2], [1, 2, 0, 2, 0], [2, 0, 1, 2, 0], [0, 0, 1, 2, 1, 0],
    [0, 1, 2, 0, 0, 1, 2], [2, 0, 2, 0, 1], [0, 0, 1, 2, 2, 1, 0], [2], [1, 2, 1],
    [0, 0, 2, 1, 0, 1], [1, 0, 0, 2, 1, 0], [2, 2], [1, 2, 1, 2, 2], [0, 2, 0, 2, 0, 1],
    [0, 1, 2, 0, 1, 2, 0], [1, 2, 2, 1], [2, 1, 2, 2, 1], [0, 2, 2, 0, 2, 0, 1],
    [1, 0, 2, 0, 2, 0], [0, 0, 1, 2, 0, 1], [1, 2, 0, 2, 0, 2], [0, 1, 2, 0, 2], [0, 0, 2, 0],
    [0, 1, 0, 2, 0], [2, 0, 1, 0, 2, 0], [0, 2, 0, 1, 2], [0, 0, 2, 2, 0]]

theorem cert_a6_gen : ∀ σ : Perm (Fin 6), σ.support.card = 3 →
    ∃ w ∈ a6cycWords, (w.map a6gen).prod = σ := by
  decide +kernel

theorem inW4_of_inW2 : ∀ y : P6, InW2 y → InW4 y := by
  decide +kernel

theorem alt6_nonabelian : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a :=
  ⟨⟨c[0, 1, 2], Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨c[1, 2, 3], Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩, by decide⟩

variable {G : Type} [Group G] [Finite G]

theorem a6CentralQuotient_of_isA6On {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) (h5 : QT13Five (↥L ⧸ CFSG.pCore 2 ↥L))
    (hA6 : IsA6On L V) : A6CentralQuotient L := by
  obtain ⟨e⟩ := hA6
  let φ : ↥L →* ↥(alternatingGroup (Fin 6)) := e.toMonoidHom.comp (autOnHom hLV)
  have hφ : Function.Surjective φ := e.surjective.comp (autOnHom_surjective hLV)
  have hO2 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxC : (x : G) ∈ centralizer (V : Set G) := hO (coe_mem_pCoreOf_iff.2 hx)
    have h1 : autOnHom hLV x = 1 := Subtype.ext (by
      rw [autOnHom_apply]
      exact A1b.conjAct_eq_one_iff.2 hxC)
    simp only [φ, MonoidHom.comp_apply, h1, map_one]
  let φ₁ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(alternatingGroup (Fin 6)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2
  have hφ₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), rfl⟩
  have hle : 360 ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [← card_alt6]
    exact Nat.card_le_card_of_surjective φ₁ hφ₁
  rcases h5 with he5 | h32 | he6 | hhat | hu
  · obtain ⟨e5⟩ := he5
    rw [Nat.card_congr e5.toEquiv, card_alt5] at hle
    omega
  · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
    rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hle
    omega
  · obtain ⟨e6⟩ := he6
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hsQ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e6).2 hs
    have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := alt6_nonabelian
      exact ⟨e6.symm a, e6.symm b, fun h => hab (by simpa using congrArg e6 h)⟩
    have hcen := center_eq_bot_of_isSimpleGroup hna
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientBot.trans e6)⟩
  · exact hhat.2.2
  · have hc := card_of_lieModel_PSU_three_three hu
    have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_lieModel_PSU hu
    rcases hs.eq_bot_or_eq_top_of_normal φ₁.ker with h | h
    · have := Nat.card_le_card_of_injective φ₁ ((MonoidHom.ker_eq_bot_iff φ₁).1 h)
      rw [hc, card_alt6] at this
      omega
    · exfalso
      have hall : ∀ y : ↥(alternatingGroup (Fin 6)), y = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := hφ₁ y
        exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top x)
      obtain ⟨a, b, hab⟩ := alt6_nonabelian
      exact hab (by rw [hall a, hall b])

open scoped IsMulCommutative in
theorem setting4_of_case_b (h1332 : Stmt13_3_2) {T L V : Subgroup G} [IsMulCommutative ↥V]
    (h : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥)
    (hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, -, -⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have ha6 : IsA6On L V := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
  have hVf := fun v (hv : v ∈ V) => mem_reducedAggregate' (hV.1 hv)
  have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTN).trans ?_
    intro k hk
    exact mem_centralizer_iff.2 fun v hv => ((hVf v hv).2.1 k hk).symm
  have hA6 := a6CentralQuotient_of_isA6On hLV hO h5 ha6
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ normalizer (V : Set G) := sup_le hLV hTV
  have hNL : normalizer (V : Set G) ≤ normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame4 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    a6 := ha6
    centralQuot := hA6
    frame := F }⟩

theorem mul_mul_of_cube {Q : Type*} [Group Q] {a : Q} (ha : a ^ 3 = 1) : a * a * (a * a) = a := by
  calc a * a * (a * a) = a ^ 3 * a := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = a := by rw [ha, one_mul]

theorem pow_two_pow_of_cube {Q : Type*} [Group Q] {a : Q} (ha : a ^ 3 = 1) (e : ℕ) :
    a ^ 2 ^ e = a ∨ a ^ 2 ^ e = a * a := by
  have h4 : a * a * (a * a) = a := mul_mul_of_cube ha
  induction e with
  | zero => left; rw [pow_zero, pow_one]
  | succ e ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h
    · right; rw [h, pow_two]
    · left; rw [h, pow_two, h4]

theorem cert_a6_tau : InD6 (swap 0 2 * swap 1 3) ∧ Perm.sign (swap (0 : Fin 6) 2 * swap 1 3) = 1 ∧
    (swap 0 2 * swap 1 3) * a6s3⁻¹ * (swap 0 2 * swap 1 3)⁻¹ = a6s3 ∧
    (swap 0 2 * swap 1 3) * (a6s3 * a6s3)⁻¹ * (swap 0 2 * swap 1 3)⁻¹ = a6s3 * a6s3 ∧
    act4f (a6s3 * a6s3) (dv 0 1) ≠ dv 0 1 := by
  decide +kernel

namespace L15A

variable {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_normalizer_pre {Y : Subgroup ↥W4} (g : ↥(normalizer (V : Set G)))
    (hY : ∀ y ∈ Y, act4 (S.frame.ρ g) y ∈ Y) : (g : G) ∈ normalizer (S.pre Y : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  obtain ⟨hxV, hxY⟩ := S.mem_pre.1 hx
  refine S.mem_pre.2 ⟨(mem_normalizer_iff.mp g.2 x).mp hxV, ?_⟩
  rw [S.psi_conj g ⟨x, hxV⟩]
  exact hY _ hxY

theorem rho_mem_alt {g : ↥(normalizer (V : Set G))} (hg : (g : G) ∈ L) :
    S.frame.ρ g ∈ alternatingGroup (Fin 6) :=
  (S.frame.image_L _).1 ⟨g, hg, rfl⟩

theorem fix_of_centralizer {Y : Subgroup ↥W4} (g : ↥(normalizer (V : Set G)))
    (hg : (g : G) ∈ centralizer (S.pre Y : Set G)) : ∀ y ∈ Y, act4 (S.frame.ρ g) y = y := by
  intro y hy
  obtain ⟨v, rfl⟩ := S.frame.ψ.surjective y
  have hv : (v : G) ∈ S.pre Y := S.mem_pre.2 ⟨v.2, by simpa using hy⟩
  refine (S.conj_eq_iff g v).1 ?_
  rw [← (mem_centralizer_iff.1 hg) v hv, mul_inv_cancel_right]

theorem isPGroup_X_ker
    {X : Subgroup G} (hXL : X ≤ L) (hXZ : X ⊓ o2Z L ≤ pCoreOf 2 L) :
    IsPGroup 2 ↥(X ⊓ centralizer (S.V2 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isPGroup_two_of_forall' fun x hx => ?_
  have hxL := hXL hx.1
  have hxN : x ∈ normalizer (V : Set G) := S.frame.L_le hxL
  have hfix : ∀ y : P6, InW2 y → act4f (S.frame.ρ ⟨x, hxN⟩) y = y := by
    intro y hy
    have h1 := L15A.fix_of_centralizer S ⟨x, hxN⟩ hx.2 ⟨y, inW4_of_inW2 y hy⟩ hy
    have h2 := congrArg Subtype.val h1
    rwa [act4_coe] at h2
  have hsq := cert_a6_C2 _
    (Perm.mem_alternatingGroup.1 (L15A.rho_mem_alt S (g := ⟨x, hxN⟩) hxL)) hfix
  have hx2 : x ^ 2 ∈ L ⊓ centralizer (V : Set G) := by
    refine mem_inf.2 ⟨pow_mem hxL 2, ?_⟩
    have h1 : S.frame.ρ (⟨x, hxN⟩ ^ 2) = 1 := by rw [map_pow, pow_two, hsq]
    exact (S.rho_eq_one_iff _).1 h1
  have hx2Z : x ^ 2 ∈ X ⊓ o2Z L := mem_inf.2 ⟨pow_mem hx.1 2, S.centralizer_le_o2Z hx2⟩
  obtain ⟨k, hk⟩ := exists_two_pow_eq_one (LieType.BorelTits.pCoreOf_isPGroup 2 L) (hXZ hx2Z)
  exact ⟨k + 1, by rw [pow_succ', pow_mul, hk]⟩

theorem V3_eq {V₃ : Subgroup G} (h23 : S.V2 ≤ V₃) (h3V : V₃ ≤ V)
    (hT3 : T ≤ normalizer (V₃ : Set G)) (hc3 : Nat.card V₃ = 8) : V₃ = S.V3 := by
  classical
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hc3, S.card_V3])
  intro x hx3
  have hxV : x ∈ V := h3V hx3
  refine S.mem_pre.2 ⟨hxV, ?_⟩
  show InW3 (S.frame.ψ ⟨x, hxV⟩ : P6)
  by_contra hy
  set y : P6 := (S.frame.ψ ⟨x, hxV⟩ : P6) with hydef
  obtain ⟨σ, hσ, hnd⟩ := cert_a6_V3 y ⟨(S.frame.ψ ⟨x, hxV⟩).2, hy⟩
  obtain ⟨hσD, hσA⟩ := DAgens_mem σ hσ
  obtain ⟨t, htT, rfl⟩ := S.frame.DA_T σ hσD hσA
  have htx : (t : G) * x * (t : G)⁻¹ ∈ V₃ := (mem_normalizer_iff.mp (hT3 htT) x).mp hx3
  let f : ↥V₃ → P6 := fun w => (S.frame.ψ ⟨w, h3V w.2⟩ : P6)
  have hf : Function.Injective f := by
    intro u w h
    have := S.frame.ψ.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (fun v : ↥V => (v : G)) this)
  have : Fintype ↥V₃ := Fintype.ofFinite _
  have hW2 : ∀ w : P6, InW2 w → ∃ u : ↥V₃, f u = w := by
    intro w hw
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨w, inW4_of_inW2 w hw⟩
    have hvV2 : (v : G) ∈ S.V2 := S.mem_pre.2 ⟨v.2, by
      show S.frame.ψ v ∈ W2sub
      rw [hv]
      exact hw⟩
    exact ⟨⟨v, h23 hvV2⟩, by simp [f, hv]⟩
  have hprod : ∀ w : P6, InW2 w → ∃ u : ↥V₃, f u = y * w := by
    intro w hw
    obtain ⟨u, hu⟩ := hW2 w hw
    refine ⟨⟨x * u, V₃.mul_mem hx3 u.2⟩, ?_⟩
    show (S.frame.ψ ⟨x * u, _⟩ : P6) = _
    rw [show (⟨x * u, h3V (V₃.mul_mem hx3 u.2)⟩ : ↥V) = ⟨x, hxV⟩ * ⟨u, h3V u.2⟩ from rfl,
      map_mul]
    show (S.frame.ψ ⟨x, hxV⟩ : P6) * (S.frame.ψ ⟨u, h3V u.2⟩ : P6) = y * w
    rw [← hu]
  have hsub : ([1, dv 0 1, dv 2 3, e0123, y, y * dv 0 1, y * dv 2 3, y * e0123,
      act4f (S.frame.ρ t) y] : List P6).toFinset ⊆ Finset.univ.image f := by
    intro u hu
    rw [List.mem_toFinset] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rw [Finset.mem_image]
    have hd01 : InW2 (dv 0 1) := Or.inr (Or.inl rfl)
    have hd23 : InW2 (dv 2 3) := Or.inr (Or.inr (Or.inl rfl))
    have he : InW2 e0123 := Or.inr (Or.inr (Or.inr rfl))
    have h1 : InW2 1 := Or.inl rfl
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨w, hw⟩ := hW2 1 h1; exact ⟨w, Finset.mem_univ _, hw⟩
    · obtain ⟨w, hw⟩ := hW2 _ hd01; exact ⟨w, Finset.mem_univ _, hw⟩
    · obtain ⟨w, hw⟩ := hW2 _ hd23; exact ⟨w, Finset.mem_univ _, hw⟩
    · obtain ⟨w, hw⟩ := hW2 _ he; exact ⟨w, Finset.mem_univ _, hw⟩
    · exact ⟨⟨x, hx3⟩, Finset.mem_univ _, rfl⟩
    · obtain ⟨w, hw⟩ := hprod _ hd01; exact ⟨w, Finset.mem_univ _, hw⟩
    · obtain ⟨w, hw⟩ := hprod _ hd23; exact ⟨w, Finset.mem_univ _, hw⟩
    · obtain ⟨w, hw⟩ := hprod _ he; exact ⟨w, Finset.mem_univ _, hw⟩
    · refine ⟨⟨(t : G) * x * (t : G)⁻¹, htx⟩, Finset.mem_univ _, ?_⟩
      show (S.frame.ψ ⟨(t : G) * x * (t : G)⁻¹, _⟩ : P6) = _
      rw [S.psi_conj t ⟨x, hxV⟩, act4_coe]
      rfl
  have h9 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_image_of_injective _ hf, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hc3] at h9
  simp at h9

theorem gen_A6 {X : Subgroup G} (hXL : X ≤ L)
    (hX : ∃ x ∈ X, ∃ hx : x ∈ normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ = a6s3 ∨ S.frame.ρ ⟨x, hx⟩ = a6s3 * a6s3) :
    autOn (X ⊔ L ⊓ normalizer (S.V3 : Set G)) V = autOn L V := by
  set A := X ⊔ L ⊓ normalizer (S.V3 : Set G) with hA
  have hAL : A ≤ L := sup_le hXL inf_le_left
  refine le_antisymm (A4.autOn_mono hAL) ?_
  set Ab : Subgroup (Perm (Fin 6)) := (A.subgroupOf (normalizer (V : Set G))).map S.frame.ρ
  have hmem : ∀ {a : G} (ha : a ∈ A) (haN : a ∈ normalizer (V : Set G)),
      S.frame.ρ ⟨a, haN⟩ ∈ Ab := fun ha haN => mem_map_of_mem _ (mem_subgroupOf.2 ha)
  obtain ⟨hs1, hs3, -, -⟩ := cert_a6_s3
  obtain ⟨hn1, hn2, hi1, hi2⟩ := cert_a6_n
  have hs : a6s3 ∈ Ab := by
    obtain ⟨x, hxX, hx, hrho⟩ := hX
    have hx' := hmem (mem_sup_left hxX) hx
    rcases hrho with h | h
    · rwa [h] at hx'
    · rw [h] at hx'
      rw [← mul_mul_of_cube hs3]
      exact mul_mem hx' hx'
  have hnN : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → (∀ y : P6, InW4 y → InW3 y → InW3 (act4f σ y)) →
      σ ∈ Ab := by
    intro σ hσ hinv
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσ)
    have hgV3 : (g : G) ∈ normalizer (S.V3 : Set G) := by
      refine L15A.mem_normalizer_pre S g fun y hy => ?_
      show InW3 ((act4 (S.frame.ρ g) y : ↥W4) : P6)
      rw [act4_coe, hg]
      exact hinv _ y.2 hy
    rw [← hg]
    exact hmem (mem_sup_right ⟨hgL, hgV3⟩) g.2
  have hgen : ∀ i, a6gen i ∈ Ab := fun i =>
    match i with
    | 0 => hs
    | 1 => hnN _ hn1 hi1
    | 2 => hnN _ hn2 hi2
  have hA6 : alternatingGroup (Fin 6) ≤ Ab := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, closure_le]
    intro σ hσ
    obtain ⟨w, -, hw⟩ := cert_a6_gen σ (Equiv.Perm.IsThreeCycle.card_support hσ)
    rw [← hw]
    refine list_prod_mem fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact hgen i
  intro f hf
  obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := mem_map.1 hf
  have hlL : l ∈ L := mem_subgroupOf.1 hl
  have hlA : S.frame.ρ ⟨l, hlN⟩ ∈ Ab := hA6 (L15A.rho_mem_alt S (g := ⟨l, hlN⟩) hlL)
  obtain ⟨⟨a, haN⟩, ha, hae⟩ := mem_map.1 hlA
  have haA : a ∈ A := mem_subgroupOf.1 ha
  have h1 : S.frame.ρ ((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, hlN⟩) = 1 := by
    rw [map_mul, map_inv, hae, inv_mul_cancel]
  have h2 := A1b.conjAct_eq_one_iff.2 ((S.rho_eq_one_iff _).1 h1)
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← h2]
  exact mem_map_of_mem _ (mem_subgroupOf.2 haA)

theorem mod_A6 : ∀ c ∈ normalizer (V : Set G) ⊓ normalizer (L : Set G) ⊓
    centralizer (S.V3 : Set G), ∀ v ∈ V, ⁅v, c⁆ ∈ fsuV1 T V := by
  intro c hc v hv
  have hcN : c ∈ normalizer (V : Set G) := hc.1.1
  set σ := S.frame.ρ ⟨c, hcN⟩ with hσ
  have hfix : ∀ y : P6, (InW4 y ∧ InW3 y) → act4f σ y = y := by
    intro y hy
    have h1 := L15A.fix_of_centralizer S ⟨c, hcN⟩ hc.2 ⟨y, hy.1⟩ hy.2
    have h2 := congrArg Subtype.val h1
    rwa [act4_coe] at h2
  have hvc := cert_a6_mod σ hfix _ (S.frame.ψ ⟨v, hv⟩).2
  have hcv : c * v * c⁻¹ ∈ V := (mem_normalizer_iff.mp hcN v).mp hv
  have hmemV : ⁅v, c⁆ ∈ V := by
    rw [commutatorElement_def, show v * c * v⁻¹ * c⁻¹ = v * (c * v * c⁻¹)⁻¹ by group]
    exact mul_mem hv (inv_mem hcv)
  have hpsi : (S.frame.ψ ⟨⁅v, c⁆, hmemV⟩ : P6) =
      (act4f σ (S.frame.ψ ⟨v, hv⟩ : P6) * (S.frame.ψ ⟨v, hv⟩ : P6)⁻¹)⁻¹ := by
    have e0 : ⁅v, c⁆ = v * (c * v * c⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    have e1 : (⟨⁅v, c⁆, hmemV⟩ : ↥V) = ⟨v, hv⟩ * (⟨c * v * c⁻¹, hcv⟩)⁻¹ := Subtype.ext e0
    rw [e1, map_mul, map_inv, S.psi_conj ⟨c, hcN⟩ ⟨v, hv⟩]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, act4_coe, mul_inv_rev, inv_inv]
    rfl
  rw [S.mem_V1_iff]
  rcases hvc with h | h
  · left
    have h1 : (S.frame.ψ ⟨⁅v, c⁆, hmemV⟩ : P6) = 1 := by rw [hpsi, h, inv_one]
    have h2 : (⟨⁅v, c⁆, hmemV⟩ : ↥V) = 1 := S.frame.ψ.injective (Subtype.ext (by
      rw [h1, map_one]; rfl))
    exact congrArg Subtype.val h2
  · right
    have h1 : (S.frame.ψ ⟨⁅v, c⁆, hmemV⟩ : P6) = e0123 := by
      rw [hpsi, h]
      decide
    have h2 : (⟨⁅v, c⁆, hmemV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (Subtype.ext (by
      rw [h1, S.psi_z]))
    exact congrArg Subtype.val h2

theorem exists_lift_s3 : ∃ g : ↥(normalizer (V : Set G)), (g : G) ∈ L ∧
    (g : G) ∈ normalizer (S.V2 : Set G) ∧ S.frame.ρ g = a6s3 ∧
    (g : G) ^ 3 ∈ centralizer (V : Set G) ∧ (g : G) ∉ centralizer (S.V2 : Set G) := by
  obtain ⟨hs1, hs3, hsW, hsm⟩ := cert_a6_s3
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L a6s3).2 (Perm.mem_alternatingGroup.2 hs1)
  refine ⟨g, hgL, ?_, hg, ?_, ?_⟩
  · refine L15A.mem_normalizer_pre S g fun y hy => ?_
    show InW2 ((act4 (S.frame.ρ g) y : ↥W4) : P6)
    rw [act4_coe, hg]
    exact hsW _ hy
  · have h1 : S.frame.ρ (g ^ 3) = 1 := by rw [map_pow, hg, hs3]
    exact (S.rho_eq_one_iff (g ^ 3)).1 h1
  · intro h
    have h1 := L15A.fix_of_centralizer S g h ⟨dv 0 1, dv_mem 0 1⟩ (Or.inr (Or.inl rfl))
    have h2 := congrArg Subtype.val h1
    rw [act4_coe, hg] at h2
    exact hsm h2

theorem exists_X_nonhat
    (hhat : ¬ IsHatA6 L) : ∃ x ∈ L₁Of L S.V2, x ^ 3 = 1 ∧
    x ∉ centralizer (S.V2 : Set G) ∧ ∃ hx : x ∈ normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ = a6s3 ∨ S.frame.ρ ⟨x, hx⟩ = a6s3 * a6s3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgL, hgV2, hg, hg3, hgc⟩ := exists_lift_s3 S
  have hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le (S.inf_centralizer_le_pCoreOf hhat)
  obtain ⟨e, hxX, hx3, hxc⟩ := exists_mem_L₁Of_cube hgL hgV2 hg3 hgc S.V2_le_V hCL
  refine ⟨_, hxX, hx3, hxc, pow_mem g.2 _, ?_⟩
  have : (⟨(g : G) ^ 2 ^ e, pow_mem g.2 _⟩ : normalizer (V : Set G)) = g ^ 2 ^ e := rfl
  rw [this, map_pow, hg]
  exact pow_two_pow_of_cube cert_a6_s3.2.1 e

end L15A

@[expose] def U3HatL2Plus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → V ⊓ centralizer (L : Set G) = ⊥ →
    IsA6On L V → IsHatA6 L → IsV2 T V V₂ →
      oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆ ⊓ o2Z L ≤ pCoreOf 2 L

namespace L15A

variable {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_TL_tau : ∃ t : ↥(normalizer (V : Set G)), (t : G) ∈ T ⊓ L ∧
    S.frame.ρ t = swap 0 2 * swap 1 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)).codRestrict _ fun l =>
      L15A.rho_mem_alt S (g := ⟨l, S.frame.L_le l.2⟩) l.2
  have hθ : Function.Surjective θ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
    exact ⟨⟨g, hgL⟩, Subtype.ext hg⟩
  have hTLs : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal
    (A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right) le_sup_left
    (sup_le le_normalizer S.T_le_NL)
  have hP1 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hTLs.2.1.of_equiv (subgroupOfEquivOfLe hTLs.1).symm
  let P : Sylow 2 ↥L := hP1.toSylow hTLs.2.2
  let Q : Sylow 2 ↥(alternatingGroup (Fin 6)) := P.mapSurjective hθ
  have hQcard : Nat.card (Q : Subgroup ↥(alternatingGroup (Fin 6))) = 8 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have h1 := Subgroup.card_mul_index (Q : Subgroup ↥(alternatingGroup (Fin 6)))
    rw [hk, card_alt6] at h1
    have h2 := Q.not_dvd_index
    have hk9 : k < 9 := by
      by_contra h
      have h3 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 h)
      have h4 : 2 ^ k ≤ 360 := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
      norm_num at h3
      omega
    rw [hk]
    interval_cases k <;> omega
  set Q' := (Q : Subgroup ↥(alternatingGroup (Fin 6))).map (alternatingGroup (Fin 6)).subtype
  have hQ'card : Nat.card Q' = 8 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective, hQcard]
  have hQ'le : Q' ≤ D6sub ⊓ alternatingGroup (Fin 6) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpT : (p : G) ∈ T := (mem_subgroupOf.1 (show p ∈ (T ⊓ L).subgroupOf L from hp)).1
    exact ⟨mem_D6sub.2 (S.frame.T_D _ hpT), (θ p).2⟩
  have hDA : Nat.card ↥(D6sub ⊓ alternatingGroup (Fin 6)) = 8 := by
    rw [Nat.card_eq_fintype_card, ← card_DA, Fintype.card_subtype]
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_inf, mem_D6sub,
      Perm.mem_alternatingGroup]
  have hQeq : Q' = D6sub ⊓ alternatingGroup (Fin 6) :=
    Subgroup.eq_of_le_of_card_ge hQ'le (by rw [hDA, hQ'card])
  obtain ⟨hτD, hτA, -⟩ := cert_a6_tau
  have hτ : swap (0 : Fin 6) 2 * swap 1 3 ∈ Q' := by
    rw [hQeq]
    exact ⟨mem_D6sub.2 hτD, Perm.mem_alternatingGroup.2 hτA⟩
  obtain ⟨q, hq, hqe⟩ := hτ
  rw [Sylow.coe_mapSurjective] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hp' := mem_subgroupOf.1 (show p ∈ (T ⊓ L).subgroupOf L from hp)
  exact ⟨⟨p, S.frame.L_le p.2⟩, hp', hqe⟩

theorem exists_X_hat
    (hP : oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ ⊓ o2Z L ≤ pCoreOf 2 L) :
    ∃ x ∈ oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆, x ^ 3 = 1 ∧ x ∉ centralizer (S.V2 : Set G) ∧
      ∃ hx : x ∈ normalizer (V : Set G),
        S.frame.ρ ⟨x, hx⟩ = a6s3 ∨ S.frame.ρ ⟨x, hx⟩ = a6s3 * a6s3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hs3, -, hsm⟩ := cert_a6_s3
  obtain ⟨-, -, hτs, hτs2, hsm2⟩ := cert_a6_tau
  obtain ⟨g, hgL, hgV2, hg, -, -⟩ := exists_lift_s3 S
  obtain ⟨t, htTL, ht⟩ := exists_TL_tau S
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  set y := (g : G) ^ 2 ^ e with hy
  have hym : y ^ m = 1 := by rw [hy, ← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hyL2 : y ∈ L₁Of L S.V2 :=
    subset_closure ⟨⟨pow_mem hgL _, pow_mem hgV2 _⟩, m, hm, hym⟩
  have hyN : y ∈ normalizer (V : Set G) := pow_mem g.2 _
  have hρy : S.frame.ρ ⟨y, hyN⟩ = a6s3 ∨ S.frame.ρ ⟨y, hyN⟩ = a6s3 * a6s3 := by
    have : (⟨y, hyN⟩ : normalizer (V : Set G)) = g ^ 2 ^ e := rfl
    rw [this, map_pow, hg]
    exact pow_two_pow_of_cube hs3 e
  set w := y * t * y⁻¹ * (t : G)⁻¹ with hw
  have hwK : w ∈ ⁅L₁Of L S.V2, T ⊓ L⁆ := Subgroup.commutator_mem_commutator hyL2 htTL
  have hwN : w ∈ normalizer (V : Set G) := mul_mem (mul_mem (mul_mem hyN t.2) (inv_mem hyN))
    (inv_mem t.2)
  have hconj : ∀ a τ : Perm (Fin 6), τ * a⁻¹ * τ⁻¹ = a → a * τ * a⁻¹ * τ⁻¹ = a * a := by
    intro a τ h
    calc a * τ * a⁻¹ * τ⁻¹ = a * (τ * a⁻¹ * τ⁻¹) := by simp only [mul_assoc]
      _ = a * a := by rw [h]
  have hρw : S.frame.ρ ⟨w, hwN⟩ = S.frame.ρ ⟨y, hyN⟩ * S.frame.ρ ⟨y, hyN⟩ := by
    have : (⟨w, hwN⟩ : normalizer (V : Set G)) = ⟨y, hyN⟩ * t * ⟨y, hyN⟩⁻¹ * t⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, ht]
    rcases hρy with h | h
    · rw [h]; exact hconj _ _ hτs
    · rw [h]; exact hconj _ _ hτs2
  have hρw' : S.frame.ρ ⟨w, hwN⟩ = a6s3 ∨ S.frame.ρ ⟨w, hwN⟩ = a6s3 * a6s3 := by
    rw [hρw]
    rcases hρy with h | h
    · right; rw [h]
    · left; rw [h, mul_mul_of_cube hs3]
  obtain ⟨e', m', hm', hnm'⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  set x := w ^ 2 ^ e' with hx
  have hxm : x ^ m' = 1 := by rw [hx, ← pow_mul, ← hnm', pow_orderOf_eq_one]
  have hxX : x ∈ oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ := subset_closure ⟨pow_mem hwK _, m', hm', hxm⟩
  have hxN : x ∈ normalizer (V : Set G) := pow_mem hwN _
  have hρx : S.frame.ρ ⟨x, hxN⟩ = a6s3 ∨ S.frame.ρ ⟨x, hxN⟩ = a6s3 * a6s3 := by
    have : (⟨x, hxN⟩ : normalizer (V : Set G)) = ⟨w, hwN⟩ ^ 2 ^ e' := rfl
    rw [this, map_pow]
    rcases hρw' with h | h
    · rw [h]; exact pow_two_pow_of_cube hs3 e'
    · rw [h]
      have h3 : (a6s3 * a6s3) ^ 3 = 1 := by
        rw [← pow_two, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hs3, one_pow]
      rcases pow_two_pow_of_cube h3 e' with h' | h'
      · right; exact h'
      · left; rw [h', mul_mul_of_cube hs3]
  refine ⟨x, hxX, ?_, ?_, hxN, hρx⟩
  ·
    have hx3C : x ^ 3 ∈ L ⊓ centralizer (V : Set G) := by
      refine mem_inf.2 ⟨pow_mem ((X_facts_L₂plus (L := L) S.T_le_NL
        S.T_le_normalizer_V2).1 hxX) 3, ?_⟩
      have h1 : S.frame.ρ (⟨x, hxN⟩ ^ 3) = 1 := by
        rw [map_pow]
        rcases hρx with h | h
        · rw [h, hs3]
        · rw [h, ← pow_two, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hs3, one_pow]
      exact (S.rho_eq_one_iff _).1 h1
    have h1 : x ^ 3 ∈ pCoreOf 2 L :=
      hP (mem_inf.2 ⟨pow_mem hxX 3, S.centralizer_le_o2Z hx3C⟩)
    obtain ⟨k, hk⟩ := exists_two_pow_eq_one (LieType.BorelTits.pCoreOf_isPGroup 2 L) h1
    have hk' : (x ^ 3) ^ m' = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
    have hcop : Nat.Coprime (2 ^ k) m' := (Nat.coprime_two_left.2 hm').pow_left k
    have h2 : orderOf (x ^ 3) ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hk')
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)
  · intro h
    have h1 := L15A.fix_of_centralizer S ⟨x, hxN⟩ h ⟨dv 0 1, dv_mem 0 1⟩ (Or.inr (Or.inl rfl))
    have h2 := congrArg Subtype.val h1
    rw [act4_coe] at h2
    rcases hρx with h' | h'
    · rw [h'] at h2; exact hsm h2
    · rw [h'] at h2; exact hsm2 h2

end L15A

theorem u3Stmt13_3_15_of_A6
    (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14)
    (hhatP : U3HatL2Plus) {T L V V₂ X I₂ : Subgroup G} (S : Setting4 G T L V)
    (hV2 : IsV2 T V V₂) (hXhat : IsHatA6 L → X = oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆)
    (hXn : ¬ IsHatA6 L → X = L₁Of L V₂)
    (hI₂ : I₂ = conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) :
    normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (A6.g1 T V) ∧
      I₂ ⊓ centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (A6.g1 T V) ⊓ centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (normalizer (V₂ : Set G)) ∧
      CFSG.pRank 3 ↥(centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          centralizer (V₃ : Set G) ≤ normalizer (V : Set G) ∧
            (¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
              ⁅V, centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V) := by
  have hV2e : V₂ = S.V2 := S.V2_unique hV2
  subst hV2e
  have hgen' : ∀ {Y : Subgroup G}, Y ≤ L → (∃ x ∈ Y, ∃ hx : x ∈ normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ = a6s3 ∨ S.frame.ρ ⟨x, hx⟩ = a6s3 * a6s3) →
      ∀ V₃ : Subgroup G, S.V2 ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) → Nat.card V₃ = 8 →
        autOn (Y ⊔ L ⊓ normalizer (V₃ : Set G)) V = autOn L V := by
    intro Y hYL hY V₃ h23 h3V hT3 hc3
    rw [L15A.V3_eq S h23 h3V hT3 hc3]
    exact L15A.gen_A6 S hYL hY
  have hmod : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → ∀ V₃ : Subgroup G, S.V2 ≤ V₃ →
      V₃ ≤ V → T ≤ normalizer (V₃ : Set G) → Nat.card V₃ = 8 →
      ∀ c ∈ normalizer (V : Set G) ⊓ normalizer (L : Set G) ⊓ centralizer (V₃ : Set G),
        ∀ v ∈ V, ⁅v, c⁆ ∈ fsuV1 T V := by
    intro _ V₃ h23 h3V hT3 hc3
    rw [L15A.V3_eq S h23 h3V hT3 hc3]
    exact L15A.mod_A6 S
  have hq1 := h13314 G T L V S.V2 S.h13 S.irr S.zv hV2 S.not_iso_a5
  by_cases hhat : IsHatA6 L
  · have hX := hXhat hhat
    subst hX
    have hP := hhatP G T L V S.V2 S.h13 S.irr S.zv S.a6 hhat hV2
    obtain ⟨hXL, hXN, hXT, hXres⟩ := X_facts_L₂plus (L := L) S.T_le_NL S.T_le_normalizer_V2
    obtain ⟨x, hxX, hx3, hxc, hx, hρx⟩ := L15A.exists_X_hat S hP
    refine (core15_of h1332 S.h13 S.irr S.zv hV2 hq1 hXL hXN hXT hXres ⟨x, hxX, hx3, hxc⟩
      (L15A.isPGroup_X_ker S hXL hP) ?_ (hgen' hXL ⟨x, hxX, hx, hρx⟩)).stmt hI₂ hmod
    intro h
    exact hxc (Subgroup.centralizer_le S.V2_le_V (S.o2Z_le_centralizer (h hxX)))
  · have hX := hXn hhat
    subst hX
    obtain ⟨hXL, hXN, hXT, hXres⟩ := X_facts_L₂ (L := L) S.T_le_NL S.T_le_normalizer_V2
    obtain ⟨x, hxX, hx3, hxc, hx, hρx⟩ := L15A.exists_X_nonhat S hhat
    have hZ : L₁Of L S.V2 ⊓ o2Z L ≤ pCoreOf 2 L :=
      inf_le_right.trans (o2Z_le_pCoreOf_of_center_eq_bot (S.center_Q_eq_bot hhat))
    refine (core15_of h1332 S.h13 S.irr S.zv hV2 hq1 hXL hXN hXT hXres ⟨x, hxX, hx3, hxc⟩
      (L15A.isPGroup_X_ker S hXL hZ) ?_ (hgen' hXL ⟨x, hxX, hx, hρx⟩)).stmt hI₂ hmod
    intro h
    exact hxc (Subgroup.centralizer_le S.V2_le_V (S.o2Z_le_centralizer (h hxX)))

end CFSG.Quasithin.H13.U3
