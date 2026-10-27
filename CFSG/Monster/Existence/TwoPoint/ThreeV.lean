module

public import CFSG.Monster.Existence.TwoPoint.Fi22
public import CFSG.Monster.Existence.TwoPoint.ThreeVConj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess

theorem fi_isConj_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a b : X} :
    IsConj (e a) (e b) ↔ IsConj a b := by
  refine ⟨fun h => ?_, fun h => e.toMonoidHom.map_isConj h⟩
  simpa using e.symm.toMonoidHom.map_isConj h

theorem fi_card_centralizer_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({b} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hb : (MulAut.conj c) a = b := by rw [MulAut.conj_apply]; exact hc
  have e : Subgroup.centralizer ({a} : Set G) ≃*
      Subgroup.centralizer ({(MulAut.conj c) a} : Set G) :=
    fiCentralizerEquiv (MulAut.conj c) a
  rw [hb] at e
  exact (Nat.card_congr e.toEquiv).symm

theorem fi_transport_class
    {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (x₀ : X) (d : Y)
    (hd : IsConj d (e x₀)) (hp : CFSG.Blueprint.Fischer.Pair Y {z | IsConj d z})
    (hcl : Nat.card {z : Y // IsConj d z} = 31671)
    (hc : Nat.card (Subgroup.centralizer ({d} : Set Y)) = 129123503308800) :
    CFSG.Blueprint.Fischer.Pair X {x | IsConj x₀ x} ∧
      (∀ γ ∈ {x : X | IsConj x₀ x},
        Nat.card (Subgroup.centralizer ({γ} : Set X)) = 129123503308800) ∧
      Nat.card {x : X // IsConj x₀ x} = 31671 := by
  refine ⟨?_, ?_, ?_⟩
  · have hset : {z : Y | IsConj d z} = {z : Y | IsConj (e x₀) z} :=
      Set.ext fun z => ⟨fun h => hd.symm.trans h, fun h => hd.trans h⟩
    have := CFSG.Sporadic.Fi23.pair_of_equiv e.toEquiv (map_mul e) (e x₀) (hset ▸ hp)
    have hs : e.toEquiv.symm (e x₀) = x₀ := e.symm_apply_apply x₀
    rwa [hs] at this
  · intro γ hγ
    have h1 : IsConj d (e γ) := hd.trans ((fi_isConj_map e).2 hγ)
    rw [← hc, ← fi_card_centralizer_of_isConj h1]
    exact Nat.card_congr (fiCentralizerEquiv e γ).toEquiv
  · rw [← hcl]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
    rw [← fi_isConj_map e]
    exact ⟨fun h => hd.trans h, fun h => hd.symm.trans h⟩

@[expose] def fiNbr : Set MGriess :=
  {γ | IsConj tGriess γ ∧ IsConj tGriess (fiAlpha * γ) ∧ IsConj tGriess (fiBeta * γ)}

theorem fiMkW_fiWAlphaGamma : fiMkW fiWAlphaGamma = fiAlpha * fiE 0 :=
  fiMkW_append fiWU[0]! fiWAlpha

theorem isConj_fiAlpha_mul_fiE_zero :
    IsConj tGriess (fiAlpha * fiE 0) := by
  have h := fiConj3VCheck_spec fiConj3VCheck_ok
  have h' : fiMkW fiCAlphaGamma * tGriess = fiMkW fiWAlphaGamma * fiMkW fiCAlphaGamma := by
    rw [← fiMkW_fiRhoT]
    exact Subtype.ext h
  rw [fiMkW_fiWAlphaGamma] at h'
  exact isConj_iff.2 ⟨fiMkW fiCAlphaGamma, by rw [h', mul_inv_cancel_right]⟩

theorem isConj_fiBeta_mul_fiE_zero :
    IsConj tGriess (fiBeta * fiE 0) := by
  have h : fiBeta * fiE 0 = fiDelta := by
    rw [fiDelta_eq]
    exact (fiE_commute_beta (by norm_num)).symm
  rw [h]
  exact isConj_fiDelta

theorem fiE_zero_mem_fiNbr :
    fiE 0 ∈ fiNbr :=
  ⟨isConj_fiE_zero, isConj_fiAlpha_mul_fiE_zero, isConj_fiBeta_mul_fiE_zero⟩

theorem fi_mul_conj_of_comm {G : Type*} [Group G] {a g x : G} (h : g * a = a * g) :
    a * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by
  calc a * (g * x * g⁻¹) = (a * g) * x * g⁻¹ := by simp only [mul_assoc]
    _ = (g * a) * x * g⁻¹ := by rw [h]
    _ = g * (a * x) * g⁻¹ := by simp only [mul_assoc]

theorem fiNbr_conj {g x : MGriess} (hg : g ∈ cent2 fiAlpha fiBeta) (hx : x ∈ fiNbr) :
    g * x * g⁻¹ ∈ fiNbr := by
  obtain ⟨hgα, hgβ⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgα hgβ
  obtain ⟨h1, h2, h3⟩ := hx
  have hc : ∀ y : MGriess, IsConj tGriess y → IsConj tGriess (g * y * g⁻¹) :=
    fun y hy => hy.trans (isConj_iff.2 ⟨g, rfl⟩)
  refine ⟨hc x h1, ?_, ?_⟩
  · rw [fi_mul_conj_of_comm hgα]
    exact hc _ h2
  · rw [fi_mul_conj_of_comm hgβ]
    exact hc _ h3

theorem fiE_zero_conj_mem_fiNbr
    {g : MGriess} (hg : g ∈ cent2 fiAlpha fiBeta) :
    g * fiE 0 * g⁻¹ ∈ fiNbr :=
  fiNbr_conj hg fiE_zero_mem_fiNbr

theorem fiK_eq_cent2_of_card
    (h : Nat.card ↥(cent2 fiAlpha fiBeta) = 4089470473293004800) :
    fiK = cent2 fiAlpha fiBeta := by
  have : Finite ↥(cent2 fiAlpha fiBeta) := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge fiK_le ?_
  rw [Nat.card_congr fiPhi.toEquiv, CFSG.Sporadic.Fi23.card_J, h]

@[expose] noncomputable def threeVPhi
    (hK : fiK = cent2 fiAlpha fiBeta) :
    ↥(cent2 fiAlpha fiBeta) ≃* CFSG.Sporadic.Fi23.J :=
  (MulEquiv.subgroupCongr hK).symm.trans fiPhi

@[expose] noncomputable def fiE0c :
    ↥(cent2 fiAlpha fiBeta) :=
  ⟨fiE 0, fiE_mem_cent2 (by norm_num)⟩

theorem threeVPhi_fiE0c
    (hK : fiK = cent2 fiAlpha fiBeta) :
    threeVPhi hK fiE0c = CFSG.Sporadic.Bridge.Fi23.img 0 := by
  have h : (MulEquiv.subgroupCongr hK).symm fiE0c = (⟨fiE 0, fiE_mem_fiK (by norm_num)⟩ : fiK) :=
    Subtype.ext rfl
  show fiPhi ((MulEquiv.subgroupCongr hK).symm fiE0c) = _
  rw [h]
  exact fiPhi_fiE (by norm_num)

theorem isConj_d_threeVPhi
    (hK : fiK = cent2 fiAlpha fiBeta) :
    IsConj CFSG.Sporadic.Fi23.d (threeVPhi hK fiE0c) := by
  rw [threeVPhi_fiE0c]
  exact isConj_iff.2 ⟨fiU, fiU_conj⟩

theorem exists_threeV_nbrs
    (hKeq : fiK = cent2 fiAlpha fiBeta)
    (htrans : ∀ b₁ ∈ {γ : MGriess | IsConj tGriess γ ∧ IsConj tGriess (fiAlpha * γ) ∧
        IsConj tGriess (fiBeta * γ)},
      ∀ b₂ ∈ {γ : MGriess | IsConj tGriess γ ∧ IsConj tGriess (fiAlpha * γ) ∧
        IsConj tGriess (fiBeta * γ)},
      ∃ g ∈ cent2 fiAlpha fiBeta, g * b₁ * g⁻¹ = b₂) :
    (∃ D : Set ↥(cent2 fiAlpha fiBeta),
      CFSG.Blueprint.Fischer.Pair ↥(cent2 fiAlpha fiBeta) D ∧
      {γ : MGriess | IsConj tGriess γ ∧ IsConj tGriess (fiAlpha * γ) ∧
        IsConj tGriess (fiBeta * γ)} = Subtype.val '' D ∧
      ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 fiAlpha fiBeta))) =
        2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
    Set.ncard {γ : MGriess | IsConj tGriess γ ∧ IsConj tGriess (fiAlpha * γ) ∧
      IsConj tGriess (fiBeta * γ)} = 31671 := by
  have htr : ∀ b₁ ∈ fiNbr, ∀ b₂ ∈ fiNbr, ∃ g ∈ cent2 fiAlpha fiBeta, g * b₁ * g⁻¹ = b₂ := htrans
  obtain ⟨hpair, hcent, hcard⟩ :=
    @fi_transport_class ↥(cent2 fiAlpha fiBeta) CFSG.Sporadic.Fi23.J inferInstance inferInstance
      (threeVPhi hKeq) fiE0c CFSG.Sporadic.Fi23.d (isConj_d_threeVPhi hKeq)
      CFSG.Sporadic.Fi23.pair_J CFSG.Sporadic.Fi23.card_class_d
      CFSG.Sporadic.Fi23.card_centralizer_d
  have hN : fiNbr = Subtype.val '' {x : ↥(cent2 fiAlpha fiBeta) | IsConj fiE0c x} := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨g, hg, hgγ⟩ := htr (fiE 0) fiE_zero_mem_fiNbr γ hγ
      exact ⟨⟨g, hg⟩ * fiE0c * ⟨g, hg⟩⁻¹, isConj_iff.2 ⟨⟨g, hg⟩, rfl⟩, hgγ⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 hx
      have hxc : (x : MGriess) = (c : MGriess) * fiE 0 * (c : MGriess)⁻¹ := by
        rw [← hc]
        rfl
      rw [hxc]
      exact fiE_zero_conj_mem_fiNbr c.2
  refine ⟨⟨{x | IsConj fiE0c x}, hpair, hN, fun γ hγ => (hcent γ hγ).trans (by norm_num)⟩, ?_⟩
  show Set.ncard fiNbr = 31671
  rw [hN, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact hcard

end CFSG.Monster.Existence
