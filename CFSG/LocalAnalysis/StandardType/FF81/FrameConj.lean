module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.Mathlib.GroupTheory.ConjCentralizer
import CFSG.GroupTheory.ConjTransport
import CFSG.Mathlib.GroupTheory.CyclicSylowZPowers

public section

namespace CFSG.StandardType.FF81

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}

private lemma map_conj_le_centralizer (hA : HypA G n b L) {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.zpowers b) :
    L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({b} : Set G) := by
  have hgb : g⁻¹ * b * g ∈ Subgroup.zpowers b := by
    simpa using CFSG.GroupTheory.mem_normalizer_zpowers_iff.mp
      (inv_mem (CFSG.GroupTheory.mem_normalizer_zpowers_iff.mpr hg))
  intro w hw
  rcases Subgroup.mem_map.mp hw with ⟨x, hxL, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [show (MulEquiv.toMonoidHom (MulAut.conj g)) x = g * x * g⁻¹ from by
    simp [MulAut.conj_apply]]
  have hxZ : x ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hA.le hxL
  have hxcomm : Commute (g⁻¹ * b * g) x :=
    Subgroup.mem_centralizer_iff.mp hxZ (g⁻¹ * b * g) hgb
  have h := Commute.map hxcomm.symm (MulAut.conj g)
  have hc : Commute (g * (x * g⁻¹)) b := by
    simpa [MulAut.conj_apply, mul_assoc] using h
  simpa [mul_assoc] using hc.eq

private lemma centralizer_le_normalizer_map_conj (hA : HypA G n b L) {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.zpowers b) :
    Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hCmap : Subgroup.centralizer ({b} : Set G) ≤
      (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_conj_centralizer_singleton, ← CFSG.GroupTheory.centralizer_zpowers_eq]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg)
  calc Subgroup.centralizer ({b} : Set G)
      ≤ (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom := hCmap
    _ ≤ (Subgroup.normalizer (L : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hA.nor
    _ ≤ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map _

private lemma map_conj_le_centralizer_of_disjoint (hA : HypA G n b L) {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.zpowers b)
    (hdisj : L ⊓ L.map (MulAut.conj g).toMonoidHom = ⊥) :
    L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (L : Set G) := by
  let L' := L.map (MulAut.conj g).toMonoidHom
  have hL'C : L' ≤ Subgroup.centralizer ({b} : Set G) := map_conj_le_centralizer hA hg
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hA.le.trans (centralizer_le_normalizer_map_conj hA hg)
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) := hL'C.trans hA.nor
  have hcomm_le : ⁅L', L⁆ ≤ L' ⊓ L :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hLN)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hL'N)
  have hcomm_bot : ⁅L', L⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine hcomm_le.trans ?_
    rw [inf_comm]
    exact hdisj.le
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot

omit [Finite G] in
private lemma orderOf_zs_coe_eq_three {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) (i : Fin 3) :
    orderOf (z i : G) = 3 := by
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime (hz.pow_z i) (hz.z_ne_one i)

private lemma conj_zs_mem_centralizer (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) {g : G} (hg : g * b * g⁻¹ ∈ Subgroup.zpowers b)
    (hdisj : L ⊓ L.map (MulAut.conj g).toMonoidHom = ⊥) (i : Fin 3) :
    g * (z i : G) * g⁻¹ ∈ Subgroup.centralizer (L : Set G) ∧
      orderOf (g * (z i : G) * g⁻¹) = 3 := by
  let L' := L.map (MulAut.conj g).toMonoidHom
  have hL'C : L' ≤ Subgroup.centralizer (L : Set G) :=
    map_conj_le_centralizer_of_disjoint hA hg hdisj
  have hmemL' : g * (z i : G) * g⁻¹ ∈ L' := by
    refine Subgroup.mem_map.mpr ⟨z i, (z i).2, ?_⟩
    simp [MulAut.conj_apply]
  refine ⟨hL'C hmemL', ?_⟩
  have h := MulEquiv.orderOf_eq (MulAut.conj g) (z i : G)
  simpa [MulAut.conj_apply] using h.trans (orderOf_zs_coe_eq_three hz i)

private lemma false_of_disjoint (hA : HypA G n b L) {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) {g : G} (hg : g * b * g⁻¹ ∈ Subgroup.zpowers b)
    (hdisj : L ⊓ L.map (MulAut.conj g).toMonoidHom = ⊥) : False := by
  let x0 : G := g * (z 0 : G) * g⁻¹
  let x1 : G := g * (z 1 : G) * g⁻¹
  obtain ⟨hx0C, hx0ord⟩ := conj_zs_mem_centralizer hA hz hg hdisj 0
  obtain ⟨hx1C, hx1ord⟩ := conj_zs_mem_centralizer hA hz hg hdisj 1
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let X0 : C := ⟨x0, hx0C⟩
  let X1 : C := ⟨x1, hx1C⟩
  have hX0ord : orderOf X0 = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hx0ord
  have hX1ord : orderOf X1 = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hx1ord
  have hcommX : Commute X0 X1 := by
    apply Subtype.ext
    change x0 * x1 = x1 * x0
    have hcommz : (z 0 : G) * (z 1 : G) = (z 1 : G) * (z 0 : G) :=
      congrArg Subtype.val (hz.comm_z 0 1)
    have h := congrArg (MulAut.conj g) hcommz
    simpa [x0, x1, MulAut.conj_apply, mul_assoc] using h
  have hmemC : X1 ∈ Subgroup.zpowers X0 := by
    rw [CFSG.GroupTheory.zpowers_eq_of_commute_of_orderOf_eq_of_isCyclic_sylow hA.cyc hX0ord hX1ord
      hcommX]
    exact Subgroup.mem_zpowers X1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemC
  have hzpow : (z 1 : G) = (z 0 : G) ^ k := by
    have hxpow : x1 = x0 ^ k := by
      simpa [X0, X1, x0, x1] using (congrArg (fun z : C => (z : G)) hk).symm
    calc
      (z 1 : G) = g⁻¹ * x1 * g := by simp [x1, mul_assoc]
      _ = g⁻¹ * x0 ^ k * g := by rw [hxpow]
      _ = (MulAut.conj g⁻¹) (x0 ^ k) := by simp [mul_assoc]
      _ = ((MulAut.conj g⁻¹) x0) ^ k := map_zpow _ _ _
      _ = (z 0 : G) ^ k := by simp [x0, mul_assoc]
  have hz1_mem : (z 1 : G) ∈ Subgroup.zpowers (z 0 : G) := by
    rw [hzpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hz1_eq : z 1 = z 0 ∨ z 1 = (z 0)⁻¹ := by
    have h := GGFF.eq_or_eq_inv_of_mem_zpowers (orderOf_zs_coe_eq_three hz 0) hz1_mem
      (by simpa using hz.z_ne_one 1)
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (by simpa using h))
  exact absurd (hz.eq_of_z_eq hz1_eq) (by decide)

theorem HypA.map_conj_eq (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.zpowers b) : L.map (MulAut.conj g).toMonoidHom = L := by
  let L' := L.map (MulAut.conj g).toMonoidHom
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hA.le.trans (centralizer_le_normalizer_map_conj hA hg)
  have hLnorm : L ≤ Subgroup.normalizer ((L ⊓ L' : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hLN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := L) (K := L'))
  have hnormal : ((L ⊓ L').subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  have hsplit := @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ hz.simple
    ((L ⊓ L').subgroupOf L) hnormal
  rcases hsplit with hbot | htop
  · exfalso
    have hdisj : Disjoint (L ⊓ L') L :=
      (Subgroup.subgroupOf_eq_bot (H := L ⊓ L') (K := L)).mp hbot
    have hbot' : L ⊓ L' = ⊥ := by
      rw [← inf_eq_left.mpr inf_le_left]
      exact hdisj.eq_bot
    exact false_of_disjoint hA hz hg hbot'
  · have hle' : L ≤ L ⊓ L' :=
      (Subgroup.subgroupOf_eq_top (H := L ⊓ L') (K := L)).mp htop
    have hle : L ≤ L' := hle'.trans inf_le_right
    have hcard : Nat.card L' = Nat.card L :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

end CFSG.StandardType.FF81
