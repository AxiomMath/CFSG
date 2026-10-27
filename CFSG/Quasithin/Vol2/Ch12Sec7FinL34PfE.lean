module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfD
public import CFSG.Quasithin.Background.B6Defs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.L34Br

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {Y : Type} [Group Y]

@[expose] def GoodPair (S E Y₁ : Subgroup Y) : Prop :=
  E ≤ S ∧ E ≤ Y₁ ∧ S ⊓ Subgroup.centralizer (E : Set Y) ≤ Y₁ ∧ IsSylowIn 2 (S ⊓ Y₁) Y₁ ∧
    IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁))) ∧ ¬ E ≤ pCoreOf 2 Y₁

theorem map_conj_eq_of_mem_centralizer {E : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.centralizer (E : Set Y)) : E.map (MulAut.conj x).toMonoidHom = E := by
  ext y
  constructor
  · rintro ⟨e, he, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 hx e he
    show x * e * x⁻¹ ∈ E
    rw [← h, mul_inv_cancel_right]
    exact he
  · intro hy
    refine ⟨y, hy, ?_⟩
    have h := Subgroup.mem_centralizer_iff.1 hx y hy
    show x * y * x⁻¹ = y
    rw [← h, mul_inv_cancel_right]

theorem map_conj_map_conj' (x y : Y) (E : Subgroup Y) :
    (E.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      E.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

theorem centralizer_conj_singleton (g x : Y) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set Y) =
      (Subgroup.centralizer ({x} : Set Y)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map_equiv,
    Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

theorem map_conj_normalizer (g : Y) (A : Subgroup Y) :
    (Subgroup.normalizer (A : Set Y)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) :=
  Subgroup.map_equiv_normalizer_eq A (MulAut.conj g)

theorem map_conj_one (E : Subgroup Y) : E.map (MulAut.conj (1 : Y)).toMonoidHom = E := by
  ext x
  simp

theorem le_normalizer_inf' {X S₁ S₂ : Subgroup Y}
    (h₁ : X ≤ Subgroup.normalizer (S₁ : Set Y)) (h₂ : X ≤ Subgroup.normalizer (S₂ : Set Y)) :
    X ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup Y) : Set Y) := by
  intro g hg
  have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₁ hg)
  have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂ hg)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, e₁, e₂]

theorem le_normalizer_inf_normal {S K : Subgroup Y} [K.Normal] :
    S ≤ Subgroup.normalizer ((S ⊓ K : Subgroup Y) : Set Y) :=
  le_normalizer_inf' Subgroup.le_normalizer
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)

theorem isPGroup_of_isElemAbelian {R : Subgroup Y} (hR : IsElemAbelian 2 R) : IsPGroup 2 R :=
  CFSG.Open.IsElemAbelian.isPGroup hR

variable [Finite Y]

theorem isPSL_oTwoUpper_quot_of_hom {W P R : Subgroup Y} (hPW : P ≤ W) (hRP : R ≤ P)
    (hWR : W ≤ Subgroup.normalizer (R : Set Y)) (hR2 : IsPGroup 2 R)
    (hpow : ∀ w ∈ W, ∃ n : ℕ, w ^ 2 ^ n ∈ P)
    {π : ↥P →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)}
    (hπs : Function.Surjective π) (hπk : π.ker = R.subgroupOf P) :
    IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥W ⧸ CFSG.pCore 2 ↥W))) ∧ P ⊓ pCoreOf 2 W ≤ R := by
  have : (R.subgroupOf P).Normal := hπk ▸ π.normal_ker
  refine isPSL_oTwoUpper_quot hPW hRP hWR hR2 hpow ?_
  exact isPSL_of_mulEquiv isPSL_psl_two_galois
    ((QuotientGroup.quotientMulEquivOfEq hπk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)).symm

theorem isPSL_oTwoUpper_quot_of_bot {W P : Subgroup Y} (hPW : P ≤ W)
    (hpow : ∀ w ∈ W, ∃ n : ℕ, w ^ 2 ^ n ∈ P) (hP : IsPSL 2 2 2 ↥P) :
    IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥W ⧸ CFSG.pCore 2 ↥W))) ∧ P ⊓ pCoreOf 2 W ≤ ⊥ := by
  have : ((⊥ : Subgroup Y).subgroupOf P).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  refine isPSL_oTwoUpper_quot hPW bot_le (fun w _ => ?_) IsPGroup.of_bot hpow ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h1
      calc h = w⁻¹ * (w * h * w⁻¹) * w := by group
        _ = 1 := by rw [h1]; group
  · exact isPSL_of_mulEquiv hP ((QuotientGroup.quotientMulEquivOfEq
      (Subgroup.bot_subgroupOf P)).trans QuotientGroup.quotientBot).symm

section Radical

variable {S R R' : Subgroup Y}

theorem map_conj_radical {x : Y}
    (hx : x ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y))
    (hR : R ≤ S ⊓ oTwoUpper ⊤) (hRe : IsElemAbelian 2 R) (hR16 : Nat.card R = 16)
    (hR'16 : Nat.card R' = 16)
    (hEA : ∀ E : Subgroup Y, E ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 E → E ≤ R ∨ E ≤ R') :
    R.map (MulAut.conj x).toMonoidHom = R ∨ R.map (MulAut.conj x).toMonoidHom = R' := by
  have hle : R.map (MulAut.conj x).toMonoidHom ≤ S ⊓ oTwoUpper ⊤ := by
    rw [← (Subgroup.mem_normalizer_iff_map_conj_eq).1 hx]
    exact Subgroup.map_mono hR
  have hc : Nat.card ↥(R.map (MulAut.conj x).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hR16]
  rcases hEA _ hle (isElemAbelian_map _ hRe) with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc, hR16]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc, hR'16]))

theorem map_conj_radical_iff (hne : R ≠ R') {x : Y}
    (hx : x ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y))
    (hR : R ≤ S ⊓ oTwoUpper ⊤) (hR' : R' ≤ S ⊓ oTwoUpper ⊤) (hRe : IsElemAbelian 2 R)
    (hR'e : IsElemAbelian 2 R') (hR16 : Nat.card R = 16) (hR'16 : Nat.card R' = 16)
    (hEA : ∀ E : Subgroup Y, E ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 E → E ≤ R ∨ E ≤ R') :
    R.map (MulAut.conj x).toMonoidHom = R ↔ R'.map (MulAut.conj x).toMonoidHom = R' := by
  have hEA' : ∀ E : Subgroup Y, E ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 E → E ≤ R' ∨ E ≤ R :=
    fun E hE hEe => (hEA E hE hEe).symm
  have hinj := Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
  constructor
  · intro h
    rcases map_conj_radical hx hR' hR'e hR'16 hR16 hEA' with h' | h'
    · exact h'
    · exact absurd (hinj (h'.trans h.symm)).symm hne
  · intro h
    rcases map_conj_radical hx hR hRe hR16 hR'16 hEA with h' | h'
    · exact h'
    · exact absurd (hinj (h'.trans h.symm)) hne

theorem isSylowIn_inf_oTwoUpper {S : Subgroup Y} (hS : IsSylowIn 2 S ⊤) :
    IsSylowIn 2 (S ⊓ oTwoUpper ⊤) (oTwoUpper (⊤ : Subgroup Y)) := by
  have : (oTwoUpper (⊤ : Subgroup Y)).Normal := oTwoUpper_top_normal'
  exact B6.isSylowTwoOf_inf_normal hS le_top (by rw [Subgroup.normalizer_eq_top])

omit [Finite Y] in
theorem isSylowIn_normalizer_inf {S : Subgroup Y} (hS : IsSylowIn 2 S ⊤) :
    IsSylowIn 2 S (Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y)) := by
  have : (oTwoUpper (⊤ : Subgroup Y)).Normal := oTwoUpper_top_normal'
  have hle : S ≤ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) :=
    le_normalizer_inf_normal
  refine ⟨hle, hS.2.1, fun h2 => hS.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S _ ⊤ hle le_top]
  exact h2.mul_right _

theorem isSylowIn_inf_normalizer_radical (hS : IsSylowIn 2 S ⊤) (hne : R ≠ R')
    (hR : R ≤ S ⊓ oTwoUpper ⊤) (hR' : R' ≤ S ⊓ oTwoUpper ⊤) (hRe : IsElemAbelian 2 R)
    (hR'e : IsElemAbelian 2 R') (hR16 : Nat.card R = 16) (hR'16 : Nat.card R' = 16)
    (hR'N : ∀ d ∈ oTwoUpper (⊤ : Subgroup Y),
      d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) →
        d ∈ Subgroup.normalizer (R' : Set Y))
    (hEA : ∀ E : Subgroup Y, E ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 E → E ≤ R ∨ E ≤ R') :
    IsSylowIn 2 (S ⊓ Subgroup.normalizer (R' : Set Y)) (Subgroup.normalizer (R' : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper (⊤ : Subgroup Y) with hK
  have hKn : K.Normal := oTwoUpper_top_normal'
  have hSK := isSylowIn_inf_oTwoUpper hS
  have hSN := isSylowIn_normalizer_inf hS
  have hEA' : ∀ E : Subgroup Y, E ≤ S ⊓ K → IsElemAbelian 2 E → E ≤ R' ∨ E ≤ R :=
    fun E hE hEe => (hEA E hE hEe).symm
  have hSKN : S ⊓ K ≤ Subgroup.normalizer (R' : Set Y) := fun d hd =>
    hR'N d (Subgroup.mem_inf.1 hd).2 (Subgroup.le_normalizer hd)
  have hSRR' : S ⊓ Subgroup.normalizer (R : Set Y) = S ⊓ Subgroup.normalizer (R' : Set Y) := by
    ext s
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hs, hsR⟩
      refine ⟨hs, Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_⟩
      exact (map_conj_radical_iff hne (le_normalizer_inf_normal hs) hR hR' hRe hR'e hR16 hR'16
        hEA).1 (Subgroup.mem_normalizer_iff_map_conj_eq.1 hsR)
    · rintro ⟨hs, hsR'⟩
      refine ⟨hs, Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_⟩
      exact (map_conj_radical_iff hne (le_normalizer_inf_normal hs) hR hR' hRe hR'e hR16 hR'16
        hEA).2 (Subgroup.mem_normalizer_iff_map_conj_eq.1 hsR')
  refine isSylowIn_of_card_le inf_le_right (hS.2.1.to_le inf_le_left) fun Q hPQ hQN hQ => ?_
  have hSKQ : S ⊓ K ≤ Q := fun x hx => hPQ (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hSKN hx⟩)
  have hQK : Q ⊓ K = S ⊓ K := (Subgroup.eq_of_le_of_card_ge (le_inf hSKQ inf_le_right)
    (card_le_of_isSylowIn hSK inf_le_right (hQ.to_le inf_le_left))).symm
  have hQN₀ : Q ≤ Subgroup.normalizer ((S ⊓ K : Subgroup Y) : Set Y) := by
    rw [← hQK]
    exact le_normalizer_inf' Subgroup.le_normalizer
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  obtain ⟨n, hnN₀, hQn⟩ := exists_conj_le_of_isSylowIn hSN hQN₀ hQ
  have hcard : Nat.card Q = Nat.card ↥(Q.map (MulAut.conj n).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj n).injective).symm
  rcases map_conj_radical hnN₀ hR' hR'e hR'16 hR16 hEA' with h | h
  · have hle : Q.map (MulAut.conj n).toMonoidHom ≤ S ⊓ Subgroup.normalizer (R' : Set Y) := by
      refine le_inf hQn ?_
      have := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hQN
      rwa [map_conj_normalizer, h] at this
    rw [hcard]
    exact Subgroup.card_le_of_le hle
  · have hle : Q.map (MulAut.conj n).toMonoidHom ≤ S ⊓ Subgroup.normalizer (R : Set Y) := by
      refine le_inf hQn ?_
      have := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hQN
      rwa [map_conj_normalizer, h] at this
    rw [hcard, ← hSRR']
    exact Subgroup.card_le_of_le hle

theorem goodPair_of_le_radical (hS : IsSylowIn 2 S ⊤) (hne : R ≠ R')
    (hR : R ≤ S ⊓ oTwoUpper ⊤) (hR' : R' ≤ S ⊓ oTwoUpper ⊤) (hRe : IsElemAbelian 2 R)
    (hR'e : IsElemAbelian 2 R') (hR16 : Nat.card R = 16) (hR'16 : Nat.card R' = 16)
    (hR'N : ∀ d ∈ oTwoUpper (⊤ : Subgroup Y),
      d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) →
        d ∈ Subgroup.normalizer (R' : Set Y))
    (hπ : ∃ π : ↥(Subgroup.normalizer (R' : Set Y) ⊓ oTwoUpper ⊤) →*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
      Function.Surjective π ∧
        π.ker = R'.subgroupOf (Subgroup.normalizer (R' : Set Y) ⊓ oTwoUpper ⊤))
    (htr : ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 → ∃ n ∈ oTwoUpper (⊤ : Subgroup Y),
      n ∈ Subgroup.normalizer (R : Set Y) ∧ n * r * n⁻¹ = s)
    (hEA : ∀ E : Subgroup Y, E ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 E → E ≤ R ∨ E ≤ R')
    {E : Subgroup Y} (hER : E ≤ R) (hE1 : E ≠ ⊥) :
    ∃ y : Y, GoodPair S (E.map (MulAut.conj y).toMonoidHom) (Subgroup.normalizer (R' : Set Y)) := by
  set K := oTwoUpper (⊤ : Subgroup Y) with hK
  have hKn : K.Normal := oTwoUpper_top_normal'
  have hEA' : ∀ E : Subgroup Y, E ≤ S ⊓ K → IsElemAbelian 2 E → E ≤ R' ∨ E ≤ R :=
    fun E hE hEe => (hEA E hE hEe).symm
  obtain ⟨y, hyR, hE'R'⟩ : ∃ y : Y, E.map (MulAut.conj y).toMonoidHom ≤ R ∧
      ¬ E.map (MulAut.conj y).toMonoidHom ≤ R' := by
    by_cases hER' : E ≤ R'
    · obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
      have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
      obtain ⟨s, hsR, hsR'⟩ : ∃ s ∈ R, s ∉ R' := by
        by_contra hc
        push Not at hc
        exact hne (Subgroup.eq_of_le_of_card_ge hc (by rw [hR16, hR'16]))
      have hs1 : s ≠ 1 := fun h => hsR' (h ▸ R'.one_mem)
      obtain ⟨n, -, hnR, hns⟩ := htr e (hER he) s hsR he1' hs1
      refine ⟨n, ?_, fun h => hsR' ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hnR x).1 (hER hx)
      · rw [← hns]
        exact h ⟨e, he, rfl⟩
    · exact ⟨1, by rw [map_conj_one]; exact hER, by rw [map_conj_one]; exact hER'⟩
  set E' := E.map (MulAut.conj y).toMonoidHom with hE'
  have hE'K : E' ≤ K := hyR.trans (hR.trans inf_le_right)
  have hE'N : E' ≤ Subgroup.normalizer (R' : Set Y) := fun x hx =>
    hR'N x (hE'K hx) (Subgroup.le_normalizer (hyR.trans hR hx))
  obtain ⟨π, hπs, hπk⟩ := hπ
  have hG := isPSL_oTwoUpper_quot_of_hom (W := Subgroup.normalizer (R' : Set Y))
    (P := Subgroup.normalizer (R' : Set Y) ⊓ K) (R := R') inf_le_left
    (le_inf Subgroup.le_normalizer (hR'.trans inf_le_right)) le_rfl
    (isPGroup_of_isElemAbelian hR'e)
    (fun w hw => by
      obtain ⟨n, hn⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup Y) (Subgroup.mem_top w)
      exact ⟨n, Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ hw _, hn⟩⟩) hπs hπk
  refine ⟨y, hyR.trans (hR.trans inf_le_left), hE'N, fun x hx => ?_,
    isSylowIn_inf_normalizer_radical hS hne hR hR' hRe hR'e hR16 hR'16 hR'N hEA, hG.1,
    fun h => hE'R' fun x hx => hG.2 (Subgroup.mem_inf.2
      ⟨Subgroup.mem_inf.2 ⟨hE'N hx, hE'K hx⟩, h hx⟩)⟩
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxN := le_normalizer_inf_normal (K := K) hxS
  rcases map_conj_radical hxN hR' hR'e hR'16 hR16 hEA' with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h
  · exfalso
    have hRx : R.map (MulAut.conj x).toMonoidHom ≠ R := fun h' =>
      hne (Subgroup.map_injective (MulAut.conj x).injective (h'.trans h.symm))
    rcases map_conj_radical hxN hR hRe hR16 hR'16 hEA with h' | h'
    · exact hRx h'
    · apply hE'R'
      have hxC' : x ∈ Subgroup.centralizer (E' : Set Y) := hxC
      rw [← map_conj_eq_of_mem_centralizer hxC', ← h']
      exact Subgroup.map_mono hyR

theorem exists_goodPair_of_le {S E : Subgroup Y} (hS : IsSylowIn 2 S ⊤) (hpar : ParY S)
    (hEK : E ≤ S ⊓ oTwoUpper ⊤) (hEe : IsElemAbelian 2 E) (hE1 : E ≠ ⊥) :
    ∃ y : Y, ∃ Y₁ : Subgroup Y, GoodPair S (E.map (MulAut.conj y).toMonoidHom) Y₁ := by
  obtain ⟨R₂, R₃, hne, hR, hEA⟩ := hpar
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR R₂ (Or.inl rfl)
  obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hR R₃ (Or.inr rfl)
  have hEA' : ∀ F : Subgroup Y, F ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 F → F ≤ R₃ ∨ F ≤ R₂ :=
    fun F hF hFe => (hEA F hF hFe).symm
  rcases hEA E hEK hEe with h | h
  · obtain ⟨y, hy⟩ := goodPair_of_le_radical hS hne h1 h1' h3 h3' h4 h4' h2' h5' h6 hEA h hE1
    exact ⟨y, _, hy⟩
  · obtain ⟨y, hy⟩ := goodPair_of_le_radical hS (Ne.symm hne) h1' h1 h3' h3 h4' h4 h2 h5 h6'
      hEA' h hE1
    exact ⟨y, _, hy⟩

end Radical

end CFSG.Quasithin.H13.L34Br
