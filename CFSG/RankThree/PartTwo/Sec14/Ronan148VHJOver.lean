module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148VJ2Over
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJ

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.RankThree.PartTwo.Sec4.Ronan148V Subgroup

theorem centralizer_zpowers_eq {X : Type*} [Group X] (w : X) :
    centralizer ((zpowers w : Subgroup X) : Set X) = centralizer ({w} : Set X) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem le_normalizer_or_eq_top_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (ψ : X ≃* X')
    {z : X} {z' : X'} (hz : zpowers (ψ z) = zpowers z')
    (h : ∀ M' : Subgroup X', centralizer ({z'} : Set X') ≤ M' →
      M' ≤ normalizer ((zpowers z' : Subgroup X') : Set X') ∨ M' = ⊤)
    {M : Subgroup X} (hM : centralizer ({z} : Set X) ≤ M) :
    M ≤ normalizer ((zpowers z : Subgroup X) : Set X) ∨ M = ⊤ := by
  have hCz' : centralizer ({z'} : Set X') = centralizer ({ψ z} : Set X') := by
    rw [← centralizer_zpowers_eq, ← hz, centralizer_zpowers_eq]
  have hCM : centralizer ({z'} : Set X') ≤ M.map ψ.toMonoidHom := by
    rw [hCz']
    intro x hx
    refine ⟨ψ.symm x, hM ?_, by simp⟩
    rw [mem_centralizer_singleton_iff] at hx ⊢
    apply ψ.injective
    simpa using hx
  rcases h _ hCM with hN | htop
  · left
    have hmap : (zpowers z).map ψ.toMonoidHom = zpowers z' := by
      rw [MonoidHom.map_zpowers]
      exact hz
    intro m hm
    have hm' : ψ m ∈ normalizer (((zpowers z).map ψ.toMonoidHom : Subgroup X') : Set X') := by
      rw [hmap]
      exact hN ⟨m, hm, rfl⟩
    rw [← map_equiv_normalizer_eq] at hm'
    obtain ⟨m', hm', he⟩ := hm'
    rwa [ψ.injective he] at hm'
  · right
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, he⟩ : ψ x ∈ M.map ψ.toMonoidHom := by rw [htop]; trivial
    rwa [ψ.injective he] at hy

section Model


theorem exists_mulEquiv_zpowers_eq {X : Type} [Group X] [Finite X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2) {z : X} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (h27 : 27 ∣ Nat.card (centralizer ({z} : Set X))) :
    ∃ ψ : X ≃* GJ, zpowers (ψ z) = zpowers zJ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXcard : Nat.card X = 604800 := KFacts.KS14.card_eq_of_j2 ⟨φ⟩
  obtain ⟨Q, hzQ, hQC⟩ := Ronan148J.exists_sylow_three_le_centralizer_of_card hz3 hXcard
    (by simpa using h27)
  set φ' : X ≃* GJ := φ.trans nativeEquivP with hφ'
  set P3X : Subgroup X := P3.map φ'.symm.toMonoidHom with hP3X
  have hP3X27 : Nat.card P3X = 27 := by
    rw [hP3X, card_map_of_injective φ'.symm.injective, card_P3]
  have hP3Xp : IsPGroup 3 P3X := IsPGroup.of_card (n := 3) (by rw [hP3X27]; norm_num)
  have hP3Xi : ¬ 3 ∣ P3X.index := by
    intro h3
    have h := P3X.index_mul_card
    rw [hP3X27, hXcard] at h
    have hi : P3X.index = 22400 := by omega
    rw [hi] at h3
    norm_num at h3
  set P3S : Sylow 3 X := hP3Xp.toSylow hP3Xi with hP3S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P3S Q
  have hQ : (Q : Subgroup X) = P3X.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sec14.coe_sylow_smul_eq_map]
    rfl
  have hzQ' := hzQ
  rw [hQ] at hzQ'
  obtain ⟨y, hyP, hyz⟩ := hzQ'
  have hyz' : g * y * g⁻¹ = z := hyz
  have hyC : ∀ w ∈ P3X, w * y = y * w := by
    intro w hw
    have hwQ : g * w * g⁻¹ ∈ (Q : Subgroup X) := by
      rw [hQ]
      exact ⟨w, hw, rfl⟩
    have hc := mem_centralizer_singleton_iff.mp (hQC hwQ)
    rw [← hyz'] at hc
    have : g * (w * y) * g⁻¹ = g * (y * w) * g⁻¹ := by
      calc g * (w * y) * g⁻¹ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * w * g⁻¹) := hc
        _ = g * (y * w) * g⁻¹ := by group
    simpa using this
  have hyP3 : φ' y ∈ P3 := by
    obtain ⟨p, hp, hpy⟩ := hyP
    rw [← hpy]
    simpa using hp
  have hyC3 : φ' y ∈ centralizer (P3 : Set GJ) := by
    rw [mem_centralizer_iff]
    intro p hp
    have h1 := hyC (φ'.symm p) ⟨p, hp, rfl⟩
    have h2 := congrArg φ' h1
    simpa using h2
  have hyZ : φ' y ∈ zpowers zJ := by
    rw [z_eq, ← inf_centralizer_P3]
    exact ⟨hyP3, hyC3⟩
  have hy1 : φ' y ≠ 1 := by
    intro h
    apply hz1
    rw [← hyz', φ'.map_eq_one_iff.mp h]
    group
  have hzJ3 : Nat.card (zpowers zJ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime z_cube zJ_ne_one]
  have hyeq : zpowers (φ' y) = zpowers zJ := by
    have hle : zpowers (φ' y) ≤ zpowers zJ := zpowers_le.mpr hyZ
    refine eq_of_le_of_card_ge hle ?_
    have hdvd : Nat.card (zpowers (φ' y)) ∣ 3 := hzJ3 ▸ card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
      exact hy1 h1
    · rw [h3, hzJ3]
  refine ⟨(MulAut.conj g⁻¹).trans φ', ?_⟩
  have hψz : ((MulAut.conj g⁻¹).trans φ') z = φ' y := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hyz']
    congr 1
    group
  rw [hψz, hyeq]

theorem khjPerfectOver_holds : Ronan148J.KHJPerfectOver := by
  intro X _ _ hX z hz1 hz3 h27 M hMp hCM
  obtain ⟨φ⟩ := hX
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_zpowers_eq φ hz1 hz3 h27
  rcases le_normalizer_or_eq_top_of_mulEquiv ψ hψ (fun M' hM' => le_normalizer_or_eq_top hM')
    hCM with hN | htop
  · exact Or.inl (le_antisymm (le_centralizer_of_isPerfect_of_le_normalizer hMp hN) hCM)
  · exact Or.inr htop

end Model

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
