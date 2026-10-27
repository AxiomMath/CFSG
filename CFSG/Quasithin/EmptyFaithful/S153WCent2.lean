module

public import CFSG.Quasithin.EmptyFaithful.S153WCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cent2

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WTwo

variable {t x : G} (X : WTwo H S L t x)
include X

theorem U0_comm_blockD {c u : G} (hc : c ∈ blockD S L) (hu : u ∈ U0 L t) : u * c = c * u := by
  have hD := X.C.D
  obtain ⟨a, ha, b, hb, rfl⟩ := hD.exists_mul_of_mem_U0 hu
  have e1 : a * c = c * a := blockD_comm_L hc (hD.blockU_le_L ha)
  have e2 : b * c = c * b := hD.blockD_comm_L₂ hc (hD.blockU2_le_L₂ hb)
  calc a * b * c = a * (b * c) := by group
    _ = a * (c * b) := by rw [e2]
    _ = (a * c) * b := by group
    _ = (c * a) * b := by rw [e1]
    _ = c * (a * b) := by group

theorem V₂_elem : IsElemAbelian 2 (conjR (blockU2 L t) x) := by
  have h := X.C'.V_elem x
  rwa [blockU_L₂] at h

theorem V₁_ab {a b : G} (ha : a ∈ conjR (blockU L) x) (hb : b ∈ conjR (blockU L) x) :
    a * b = b * a := X.C.V_comm ha hb

theorem V₂_ab {a b : G} (ha : a ∈ conjR (blockU2 L t) x) (hb : b ∈ conjR (blockU2 L t) x) :
    a * b = b * a :=
  (C5.isElemAbelian_two_iff.mp X.V₂_elem).1 a ha b hb

theorem centralizer_U0x_le {r : G} (hr : r ∈ S)
    (h1 : ∀ v ∈ conjR (blockU L) x, r * v = v * r)
    (h2 : ∀ v ∈ conjR (blockU2 L t) x, r * v = v * r) :
    ∃ w ∈ conjR (blockU L) x ⊔ conjR (blockU2 L t) x, ∃ c ∈ blockD S L, r = w * c := by
  have hD := X.C.D
  have hrS₁ : r ∈ s2SI S L := X.mem_s2SI_of_comm_V₁ hr h1
  obtain ⟨v₁, hv₁, hrv₁⟩ :=
    exists_mul_of_comm_pi X.C.P.toPiData (X.C.V_le_N X.hx) X.hVE hrS₁.2 h1
  have hv₁B : v₁ ∈ baum S := X.C.V_le_baum X.hx hv₁
  have hv₁S₁ : v₁ ∈ s2SI S L := ⟨hv₁B.1, X.C.hBN hv₁B⟩
  have hr₁S₁ : v₁⁻¹ * r ∈ s2SI S L := (s2SI S L).mul_mem ((s2SI S L).inv_mem hv₁S₁) hrS₁
  have hr₁V₂ : ∀ v ∈ conjR (blockU2 L t) x, (v₁⁻¹ * r) * v = v * (v₁⁻¹ * r) := by
    intro v hv
    have c1 : Commute v₁ v := X.V₁_comm_V₂ hv₁ hv
    have c2 : Commute r v := h2 v hv
    exact (c1.inv_left.mul_left c2).eq
  have hV₂N : conjR (blockU2 L t) x ≤ normalizer ((conjR L t : Subgroup G) : Set G) := by
    have h := X.C'.V_le_N X.hx
    rwa [blockU_L₂] at h
  obtain ⟨v₂, hv₂, hrv₂⟩ := exists_mul_of_comm_pi X.C'.P.toPiData hV₂N X.hVE₂
    (hD.s2SI_le_normalizer_L₂ hr₁S₁) hr₁V₂
  rw [blockU_L₂] at hrv₂
  have hv₂B : v₂ ∈ baum S := by
    have h := X.C'.V_le_baum X.hx
    rw [blockU_L₂] at h
    exact h hv₂
  have hr₂S : v₂⁻¹ * (v₁⁻¹ * r) ∈ S :=
    S.mul_mem (S.inv_mem hv₂B.1) (S.mul_mem (S.inv_mem hv₁B.1) hr)
  have hr₂U₁ : ∀ a ∈ blockU L, a * (v₂⁻¹ * (v₁⁻¹ * r)) = (v₂⁻¹ * (v₁⁻¹ * r)) * a := by
    intro a ha
    have c1 : Commute a v₂⁻¹ := (show Commute a v₂ from (X.V₂_comm_U₁ hv₂ ha).symm).inv_right
    have c2 : Commute a (v₁⁻¹ * r) := (hrv₁ a ha).symm
    exact (c1.mul_right c2).eq
  have hr₂U₂ : ∀ b ∈ blockU2 L t, b * (v₂⁻¹ * (v₁⁻¹ * r)) = (v₂⁻¹ * (v₁⁻¹ * r)) * b :=
    fun b hb => (hrv₂ b hb).symm
  have hr₂P : v₂⁻¹ * (v₁⁻¹ * r) ∈ pCoreOf 2 H := by
    rw [← hD.campbell_pkg.2.2.2]
    exact ⟨hr₂S, Subgroup.mem_centralizer_iff.2 (hD.U0_comm_of hr₂U₁ hr₂U₂)⟩
  obtain ⟨u, hu, c, hc, hrc⟩ := X.P_decomp hr₂P
  have hu_eq : u = (v₂⁻¹ * (v₁⁻¹ * r)) * c⁻¹ := by rw [hrc]; group
  have hu₁ : ∀ v ∈ conjR (blockU L) x, u * v = v * u := by
    intro v hv
    have c1 : Commute (v₂⁻¹ * (v₁⁻¹ * r)) v := by
      have d1 : Commute v₂ v := (X.V₁_comm_V₂ hv hv₂).symm
      have d2 : Commute v₁ v := X.V₁_ab hv₁ hv
      have d3 : Commute r v := h1 v hv
      exact d1.inv_left.mul_left (d2.inv_left.mul_left d3)
    have c2 : Commute c⁻¹ v := (show Commute c v from X.blockD_comm_V₁ hc hv).inv_left
    rw [hu_eq]
    exact (c1.mul_left c2).eq
  have hu₂ : ∀ v ∈ conjR (blockU2 L t) x, u * v = v * u := by
    intro v hv
    have c1 : Commute (v₂⁻¹ * (v₁⁻¹ * r)) v := by
      have d1 : Commute v₂ v := X.V₂_ab hv₂ hv
      have d2 : Commute v₁ v := X.V₁_comm_V₂ hv₁ hv
      have d3 : Commute r v := h2 v hv
      exact d1.inv_left.mul_left (d2.inv_left.mul_left d3)
    have c2 : Commute c⁻¹ v := (show Commute c v from X.blockD_comm_V₂ hc hv).inv_left
    rw [hu_eq]
    exact (c1.mul_left c2).eq
  obtain ⟨a, ha, b, hb, hab⟩ := hD.exists_mul_of_mem_U0 hu
  have haV : a ∈ conjR (blockU L) x := by
    have h1' : a ∈ blockU L ⊓ centralizer (conjR (blockU L) x : Set G) := by
      refine Subgroup.mem_inf.2 ⟨ha, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      have hb' : v * b = b * v := X.V₁_comm_U₂ hv hb
      have hu' : a * b * v = v * (a * b) := by rw [hab]; exact hu₁ v hv
      have key : (a * v) * b = (v * a) * b := by
        calc (a * v) * b = a * (v * b) := by group
          _ = a * (b * v) := by rw [hb']
          _ = (a * b) * v := by group
          _ = v * (a * b) := hu'
          _ = (v * a) * b := by group
      exact (mul_right_cancel key).symm
    rw [X.cent_U₁_V₁.1] at h1'
    exact (Subgroup.mem_inf.1 h1').2
  have hbV : b ∈ conjR (blockU2 L t) x := by
    have h2' : b ∈ blockU2 L t ⊓ centralizer (conjR (blockU2 L t) x : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hb, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      have ha' : v * a = a * v := X.V₂_comm_U₁ hv ha
      have hu' : a * b * v = v * (a * b) := by rw [hab]; exact hu₂ v hv
      have key : a * (b * v) = a * (v * b) := by
        calc a * (b * v) = (a * b) * v := by group
          _ = v * (a * b) := hu'
          _ = (v * a) * b := by group
          _ = (a * v) * b := by rw [ha']
          _ = a * (v * b) := by group
      exact (mul_left_cancel key).symm
    rw [X.cent_U₂_V₂.1] at h2'
    exact (Subgroup.mem_inf.1 h2').2
  refine ⟨v₁ * v₂ * (a * b), ?_, c, hc, ?_⟩
  · exact (conjR (blockU L) x ⊔ conjR (blockU2 L t) x).mul_mem
      ((conjR (blockU L) x ⊔ conjR (blockU2 L t) x).mul_mem (Subgroup.mem_sup_left hv₁)
        (Subgroup.mem_sup_right hv₂))
      ((conjR (blockU L) x ⊔ conjR (blockU2 L t) x).mul_mem (Subgroup.mem_sup_left haV)
        (Subgroup.mem_sup_right hbV))
  · calc r = v₁ * (v₂ * (v₂⁻¹ * (v₁⁻¹ * r))) := by group
      _ = v₁ * (v₂ * (u * c)) := by rw [hrc]
      _ = v₁ * v₂ * (a * b) * c := by rw [hab]; group

theorem conjR_pCoreOf : conjR (pCoreOf 2 H) x = S ⊓ centralizer (conjR (U0 L t) x : Set G) := by
  have h := X.C.D.campbell_pkg.2.2.2
  rw [← h]
  show conjSubgroup (S ⊓ centralizer ((U0 L t : Subgroup G) : Set G)) x = _
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_eq_self X.hx]
  rfl

theorem frattiniOf_pCoreOf :
    CFSG.QuasithinUnique.DoubleA3.frattiniOf (pCoreOf 2 H) =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) := by
  have hD := X.C.D
  have hab := C5.isElemAbelian_two_iff.mp hD.U0_isElemAbelian
  exact frattiniOf_eq_of_mul (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    hD.blockD_le_pCoreOf hab.1 hab.2 (fun w hw d hd => X.U0_comm_blockD hd hw)
    (fun e he => X.P_decomp he)

theorem frattiniOf_centralizer_U0x :
    CFSG.QuasithinUnique.DoubleA3.frattiniOf (S ⊓ centralizer (conjR (U0 L t) x : Set G)) =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) := by
  have hD := X.C.D
  have hab := C5.isElemAbelian_two_iff.mp
    (C5.isElemAbelian_two_iff.mpr ((C5.isElemAbelian_two_iff.mp hD.U0_isElemAbelian).conjSubgroup x))
  have hcV : ∀ w ∈ conjR (U0 L t) x, ∀ d ∈ blockD S L, w * d = d * w := by
    intro w hw d hd
    rw [conjR_U0_eq L t x] at hw
    exact comm_sup_left (A₁ := conjR (blockU L) x) (A₂ := conjR (blockU2 L t) x)
      (B := blockD S L) (fun a ha b hb => (X.blockD_comm_V₁ hb ha).symm)
      (fun a ha b hb => (X.blockD_comm_V₂ hb ha).symm) w hw d hd
  refine frattiniOf_eq_of_mul (W := conjR (U0 L t) x) (hD.hcs.sylow.isPGroup.to_le inf_le_left) ?_ hab.1 hab.2 hcV ?_
  · intro d hd
    exact ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun w hw => hcV w hw d hd⟩
  · intro e he
    have h1 : ∀ v ∈ conjR (blockU L) x, e * v = v * e := fun v hv =>
      (Subgroup.mem_centralizer_iff.1 he.2 v (by
        rw [conjR_U0_eq L t x]; exact Subgroup.mem_sup_left hv)).symm
    have h2 : ∀ v ∈ conjR (blockU2 L t) x, e * v = v * e := fun v hv =>
      (Subgroup.mem_centralizer_iff.1 he.2 v (by
        rw [conjR_U0_eq L t x]; exact Subgroup.mem_sup_right hv)).symm
    obtain ⟨w, hw, c, hc, rfl⟩ := X.centralizer_U0x_le he.1 h1 h2
    exact ⟨w, by show w ∈ conjR (U0 L t) x; rw [conjR_U0_eq L t x]; exact hw, c, hc, rfl⟩

theorem conjR_frattiniOf_blockD :
    conjR (CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L)) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) := by
  calc conjR (CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L)) x
      = conjR (CFSG.QuasithinUnique.DoubleA3.frattiniOf (pCoreOf 2 H)) x := by
        rw [X.frattiniOf_pCoreOf]
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf (conjR (pCoreOf 2 H) x) :=
        conjSubgroup_frattiniOf (pCoreOf 2 H) x
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf (S ⊓ centralizer (conjR (U0 L t) x : Set G)) := by
        rw [X.conjR_pCoreOf]
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) := X.frattiniOf_centralizer_U0x

theorem frattiniOf_blockD : CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) = ⊥ := by
  have hD := X.C.D
  by_contra hne
  refine X.hC52 _ ?_ hne ?_ ?_
  · exact (Subgroup.map_subtype_le _).trans inf_le_left
  · intro h hh
    exact mem_normalizer_frattiniOf (hD.H_le_normalizer_blockD hh)
  · intro m hm
    by_cases hmS : m ∈ S
    · exact mem_normalizer_frattiniOf (R := blockD S L) (S_le_normalizer_blockD (L := L) hmS)
    · have hs : x⁻¹ * m ∈ S := inv_mul_mem_of_relIndex_two X.h2 X.hxM X.hxS hm hmS
      have hxN : x ∈ normalizer ((CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) :
          Subgroup G) : Set G) := Lin2.conjR_eq_self_iff.1 X.conjR_frattiniOf_blockD
      have hsN := mem_normalizer_frattiniOf (R := blockD S L) (S_le_normalizer_blockD (L := L) hs)
      have e : m = x * (x⁻¹ * m) := by group
      rw [e]
      exact (normalizer ((CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) :
        Subgroup G) : Set G)).mul_mem hxN hsN

theorem blockD_isElemAbelian : IsElemAbelian 2 (blockD S L) := by
  have hD := X.C.D
  have hD2 : IsPGroup 2 ↥(blockD S L) := hD.hcs.sylow.isPGroup.to_le inf_le_left
  have hΦ := X.frattiniOf_blockD
  refine C5.isElemAbelian_two_iff.mpr ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h1 : ⁅a, b⁆ ∈ CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) :=
      CFSG.QuasithinUnique.DoubleA3.commutator_le_frattiniOf hD2
        (Subgroup.commutator_mem_commutator ha hb)
    rw [hΦ, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · have h1 : a ^ 2 ∈ CFSG.QuasithinUnique.DoubleA3.frattiniOf (blockD S L) :=
      sq_mem_frattiniOf hD2 ha
    rw [hΦ, Subgroup.mem_bot] at h1
    exact h1

theorem blockD_le_baum : blockD S L ≤ baum S := by
  intro c hc
  refine Subgroup.mem_inf.2 ⟨hc.1, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
  have hzP : z ∈ pCoreOf 2 H := X.C.D.omegaOneCenter_le_pCoreOf X.C.P.toPiData hz
  obtain ⟨u, hu, c₀, hc₀, rfl⟩ := X.P_decomp hzP
  have e1 : u * c = c * u := X.U0_comm_blockD hc hu
  have e2 : c₀ * c = c * c₀ := (C5.isElemAbelian_two_iff.mp X.blockD_isElemAbelian).1 c₀ hc₀ c hc
  calc u * c₀ * c = u * (c₀ * c) := by group
    _ = u * (c * c₀) := by rw [e2]
    _ = (u * c) * c₀ := by group
    _ = (c * u) * c₀ := by rw [e1]
    _ = c * (u * c₀) := by group

theorem baumD_eq_blockD : baumD S L = blockD S L :=
  le_antisymm (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => ⟨X.blockD_le_baum hc, hc.2⟩)

end WTwo

end CFSG.QuasithinUnique.AppCS2W
