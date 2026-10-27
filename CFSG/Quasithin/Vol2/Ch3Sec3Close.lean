module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3327
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

variable {G : Type} [Group G]

noncomputable abbrev preimageA2 (T L : Subgroup G)
    (φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6)) : Subgroup G :=
  preimageAut T (vPlus L T) ((aBar2.map φ.symm.toMonoidHom).map (autOn (L ⊔ T) (vPlus L T)).subtype)

@[expose] def InspClose : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → IsAltBlockType L 6 → tC L T = ⊥ →
    ((qL L T = vPlus L T ∧ ∃ _ : IsMulCommutative ↥(vPlus L T),
        XMod.IsIrrSec ↥(autOn L (vPlus L T)) (⊥ : Subgroup ↥(vPlus L T)) ⊤) ∨
      (∃ _ : IsMulCommutative ↥(qL L T), Nat.card ↥(qL L T) = 2 ^ 5 ∧
        permQuot6Model.Realizes (autOn (L ⊔ T) (qL L T)) ⊤ ⊥)) →
    ∀ φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6),
      ((autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T))).map φ.toMonoidHom =
        sylowS6 →
      (∀ B : Subgroup G, B ≤ preimageA2 T L φ → IsElemAbelian 2 B →
        Nat.card ↥B ≤ Nat.card ↥(qL L T)) ∧
      (∀ B : Subgroup G, IsMaxElemAbelian (preimageA2 T L φ) B → ¬ B ≤ qL L T →
        ∃ b ∈ B, qL L T ⊓ Subgroup.centralizer (B : Set G) =
          qL L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      ∀ B B' : Subgroup G, IsMaxElemAbelian (preimageA2 T L φ) B →
        IsMaxElemAbelian (preimageA2 T L φ) B' → ¬ B ≤ qL L T → ¬ B' ≤ qL L T →
        Nat.card ↥(B ⊔ qL L T) = Nat.card ↥(B' ⊔ qL L T) → B ⊔ qL L T = B' ⊔ qL L T

theorem autOn_sup_eq_of_comm {X Q : Subgroup G} (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) : autOn (X ⊔ Q) Q = autOn X Q := by
  refine le_antisymm ?_ (InternalSec.autOn_le_autOn_of_le le_sup_left)
  intro φ hφ
  obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hφ
  rw [sup_comm] at hy
  obtain ⟨q, hq, x, hx, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hXQ).mp hy
  have hqN : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq
  have hxN : x ∈ Subgroup.normalizer (Q : Set G) := hXQ hx
  have hqC : q ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz q hq
  have e : (⟨q * x, hyN⟩ : Subgroup.normalizer (Q : Set G)) = ⟨q, hqN⟩ * ⟨x, hxN⟩ := rfl
  rw [e, map_mul, InternalSec.conjAct_eq_one_of_mem_centralizer ⟨q, hqN⟩ hqC, one_mul]
  exact CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨x, hxN⟩, hx, rfl⟩

theorem map_conj_map_conj (Q : Subgroup G) (a b : G) :
    (Q.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      Q.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply]
  group

theorem map_conj_one (Q : Subgroup G) : Q.map (MulAut.conj (1 : G)).toMonoidHom = Q := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one,
    mul_one]
  exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

variable [Finite G] {T M L D : Subgroup G}

theorem stmt3_3_close_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h30 : Stmt3_3_30) (h31 : Stmt3_3_31) (h32 : Stmt3_3_32) (hI : InspClose) :
    Stmt3_3_Close := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hA6 := h30 G T M L D h
  have hTC := h31 G T M L D h
  obtain ⟨hc1, -, φ, hφT, hDT₀⟩ := h32 G T M L D h
  obtain ⟨ha, hb, hc⟩ := hI G T M L D h hTL hA6 hTC hc1 φ hφT
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hFQ := h.frattini_qL_le_tC h38 h39 hA6.1 hTL
  rw [hTC] at hFQ
  have hF : frattini ↥(qL L T) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (qL L T).subtype_injective).mp (le_bot_iff.mp hFQ)
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hQT₀ : qL L T ≤ preimageA2 T L φ := by
    intro q hq
    refine Subgroup.mem_inf.mpr ⟨hQT hq, ⟨⟨q, hTV (hQT hq)⟩, ?_, rfl⟩⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [InternalSec.conjAct_eq_one_of_mem_centralizer _ (hQC hq)]
    exact Subgroup.one_mem _
  have hT₀T : preimageA2 T L φ ≤ T := inf_le_left
  have hT₀N : preimageA2 T L φ ≤ Subgroup.normalizer (qL L T : Set G) :=
    hT₀T.trans (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hT₀C : preimageA2 T L φ ⊓ Subgroup.centralizer (qL L T : Set G) = qL L T := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQT₀ fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz y hy)
    rw [← hCQ]
    exact ⟨hT₀T (Subgroup.mem_inf.mp hx).1,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) (Subgroup.mem_inf.mp hx).2⟩
  have hQmax : IsMaxElemAbelian (preimageA2 T L φ) (qL L T) := ⟨hQT₀, hQe, ha⟩
  have hperm : ∀ g ∈ D, ∀ B, IsMaxElemAbelian (preimageA2 T L φ) B →
      IsMaxElemAbelian (preimageA2 T L φ) (B.map (MulAut.conj g).toMonoidHom) := by
    intro g hg B hB
    have hT₀g : (preimageA2 T L φ).map (MulAut.conj g).toMonoidHom = preimageA2 T L φ :=
      A38.map_conj_eq_iff.mpr (hDT₀ hg)
    have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr hB
    rwa [hT₀g] at this
  have hQne : qL L T ≠ ⊥ := h.toSetup331.pCoreOf_ne_bot
  have hDQ : ¬ D ≤ Subgroup.normalizer (qL L T : Set G) :=
    h.not_le_normalizer h38 h39 hQne (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨d, hdD, hdQ⟩ := IsConcreteLE.not_le_iff_exists.mp hDQ
  have hdQ' : d⁻¹ ∉ Subgroup.normalizer (qL L T : Set G) := fun h' => hdQ (by
    simpa using inv_mem h')
  have hnot : ∀ g : G, g ∉ Subgroup.normalizer (qL L T : Set G) →
      ¬ (qL L T).map (MulAut.conj g).toMonoidHom ≤ qL L T := by
    intro g hg hle
    apply hg
    refine A38.map_conj_eq_iff.mp (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hQ₁ := hperm d hdD _ hQmax
  have hQ₂ := hperm d⁻¹ (inv_mem hdD) _ hQmax
  have hcard : Nat.card ↥((qL L T).map (MulAut.conj d).toMonoidHom ⊔ qL L T) =
      Nat.card ↥((qL L T).map (MulAut.conj d⁻¹).toMonoidHom ⊔ qL L T) := by
    have e : ((qL L T).map (MulAut.conj d).toMonoidHom ⊔ qL L T).map
        (MulAut.conj d⁻¹).toMonoidHom = (qL L T).map (MulAut.conj d⁻¹).toMonoidHom ⊔ qL L T := by
      rw [Subgroup.map_sup, map_conj_map_conj, inv_mul_cancel, map_conj_one, sup_comm]
    rw [← e, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective]
  have hsup := hc _ _ hQ₁ hQ₂ (hnot d hdQ) (hnot d⁻¹ hdQ') hcard
  obtain ⟨b, hbQ₁, hbC⟩ := hb _ hQ₁ (hnot d hdQ)
  have hauto : autI hQe ((qL L T).map (MulAut.conj d).toMonoidHom) =
      autI hQe ((qL L T).map (MulAut.conj d⁻¹).toMonoidHom) := by
    rw [autI_eq_autOn, autI_eq_autOn, ← autOn_sup_eq_of_comm hQab (hQ₁.1.trans hT₀N), hsup,
      autOn_sup_eq_of_comm hQab (hQ₂.1.trans hT₀N)]
  have heq := B2_21 hQe hQT₀ hT₀N hT₀C hQ₁ hbQ₁ hbC hQ₂ hauto
  have hd2 : d ^ 2 ∈ Subgroup.normalizer (qL L T : Set G) := by
    refine A38.map_conj_eq_iff.mp ?_
    have h1 := congrArg (fun X : Subgroup G => X.map (MulAut.conj d).toMonoidHom) heq
    simp only [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h1
    rw [pow_two, ← h1]
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  exact hdQ ((Subgroup.zpowers_le.mpr hd2) (mem_zpowers_sq_of_odd hodd))

theorem stmt3_3_1A_of_inputs
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h30 : Stmt3_3_30) (h31 : Stmt3_3_31) (h32 : Stmt3_3_32) (hI : InspClose) : Stmt3_3_1A :=
  stmt3_3_1A_of_close (stmt3_3_close_of h38 h39 h14 h30 h31 h32 hI)

end CFSG.Quasithin.H13
