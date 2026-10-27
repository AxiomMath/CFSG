module

public import CFSG.Quasithin.EmptyFaithful.S153YGMate

public section

namespace CFSG.Quasithin.YG.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace GCfg

variable {H S L : Subgroup G} (C : GCfg H S L)
include C

theorem hL : IsShort2 L := C56.isShort C.hcs

theorem U_le_K : C.U ≤ conjJoin S L := by
  rw [C.hUdef]
  refine iSup_mono fun s => Subgroup.map_mono ?_
  exact (C1.blockU_le_blockQ C.hL).trans (C1.blockQ_le L)

omit [Finite G] C in
theorem conj_mem_blockD {s d : G} (hs : s ∈ S) (hd : d ∈ blockD S L) :
    s * d * s⁻¹ ∈ blockD S L := by
  have hsd : s * d * s⁻¹ ∈ S := mul_mem (mul_mem hs hd.1) (inv_mem hs)
  refine ⟨hsd, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
  have hk' : s⁻¹ * k * s ∈ conjJoin S L := by
    have := (Subgroup.mem_normalizer_iff.1 (C56.S_le_normalizer_conjJoin L (inv_mem hs)) k).1 hk
    simpa using this
  have h := Subgroup.mem_centralizer_iff.1 hd.2 _ hk'
  calc k * (s * d * s⁻¹) = s * ((s⁻¹ * k * s) * d) * s⁻¹ := by group
    _ = s * (d * (s⁻¹ * k * s)) * s⁻¹ := by rw [h]
    _ = (s * d * s⁻¹) * k := by group

omit [Finite G] C in
theorem S_le_N_D : S ≤ Subgroup.normalizer (blockD S L : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact fun hd => GCfg.conj_mem_blockD hs hd
  · intro h
    have := GCfg.conj_mem_blockD (inv_mem hs) h
    simpa [mul_assoc] using this

theorem D_le_Q : blockD S L ≤ pCoreOf 2 H := by
  rw [C.hQeq]; exact le_sup_right

theorem Q_eq : pCoreOf 2 H = C.U ⊔ blockD S L := C.hQeq

theorem U_comm_D {u d : G} (hu : u ∈ C.U) (hd : d ∈ blockD S L) : u * d = d * u :=
  Subgroup.mem_centralizer_iff.1 hd.2 u (C.U_le_K hu)

theorem exists_UD {q : G} (hq : q ∈ pCoreOf 2 H) : ∃ u ∈ C.U, ∃ d ∈ blockD S L, q = u * d := by
  rw [C.hQeq] at hq
  obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute (fun u hu d hd => C.U_comm_D hu hd) hq
  exact ⟨u, hu, d, hd, rfl⟩

theorem U_inf_D : C.U ⊓ blockD S L = ⊥ := C.hUD

end GCfg

namespace GMate

variable {H S L M₀ : Subgroup G} {x : G} (C : GCfg H S L) (m : GMate H S M₀ x)
include C m

omit [Finite G] C in
theorem S_le_N_conj {D : Subgroup G} (hD : S ≤ Subgroup.normalizer (D : Set G)) :
    S ≤ Subgroup.normalizer (conjSubgroup D x : Set G) := by
  intro s hs
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup]
  have e : x * s = (x * s * x⁻¹) * x := by group
  rw [e, ← conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self (hD (m.conj_mem_S hs))]

omit [Finite G] C in
theorem conj_conj_eq {D : Subgroup G} (hD : S ≤ Subgroup.normalizer (D : Set G)) :
    conjSubgroup (conjSubgroup D x) x = D := by
  rw [conjSubgroup_conjSubgroup]
  exact C5.conjSubgroup_eq_self (hD m.xx)

theorem D_comm_V {d v : G} (hd : d ∈ blockD S L) (hv : v ∈ conjR (C.U) x) :
    d * v = v * d := by
  have h1 : d * v * d⁻¹ * v⁻¹ ∈ blockD S L := by
    have := mul_mem hd (GCfg.conj_mem_blockD (m.V_le_S C hv) (inv_mem hd))
    simpa [mul_assoc] using this
  have h2 : d * v * d⁻¹ * v⁻¹ ∈ conjR (C.U) x := by
    have h3 := (Subgroup.mem_normalizer_iff.1 (m.S_le_N_V C hd.1) v).1 hv
    exact mul_mem h3 (inv_mem hv)
  have h4 : d * v * d⁻¹ * v⁻¹ ∈ pCoreOf 2 H := C.D_le_Q h1
  have h5 := m.V_inf_Q_le_U C h2 h4
  have h6 : d * v * d⁻¹ * v⁻¹ ∈ C.U ⊓ blockD S L := ⟨h5, h1⟩
  rw [C.U_inf_D, Subgroup.mem_bot] at h6
  calc d * v = (d * v * d⁻¹ * v⁻¹) * (v * d) := by group
    _ = v * d := by rw [h6, one_mul]

@[expose] def GK (U S : Subgroup G) (x : G) : Subgroup G :=
  S ⊓ Subgroup.centralizer ((U ⊔ conjR U x : Subgroup G) : Set G)

theorem conj_K : conjSubgroup (GK C.U S x) x = GK C.U S x := by
  unfold GK
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_sup,
    C5.conjSubgroup_eq_self m.xN]
  have h1 : conjSubgroup (conjR C.U x) x = C.U := m.V_conj C
  rw [h1, sup_comm]
  rfl

theorem D_le_K : blockD S L ≤ GK C.U S x := by
  intro d hd
  refine ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have hU : C.U ≤ Subgroup.centralizer ({d} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (C.U_comm_D hu hd).symm
  have hV : conjR (C.U) x ≤ Subgroup.centralizer ({d} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact m.D_comm_V C hd hv
  have := Subgroup.mem_centralizer_iff.1 ((sup_le hU hV) hy) d (Set.mem_singleton d)
  exact this.symm

theorem sqSub_K : C5.sqSub (GK C.U S x) = C5.sqSub (blockD S L) := by
  apply le_antisymm
  · refine C5.sqSub_le_of_forall fun k hk => ?_
    have hkS : k ∈ S := hk.1
    have hkU : k ∈ Subgroup.centralizer (C.U : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hk.2
    have hkQ : k ∈ pCoreOf 2 H := by rw [← C.hQ]; exact ⟨C.hSH hkS, hkU⟩
    obtain ⟨u, hu, d, hd, rfl⟩ := C.exists_UD hkQ
    have hc : Commute u d := C.U_comm_D hu hd
    have hu2 : u ^ 2 = 1 := C.hU.2 u hu
    rw [hc.mul_pow, hu2, one_mul]
    exact C5.sq_mem_sqSub hd
  · exact C5.sqSub_mono (m.D_le_K C)

theorem sqSub_D : C5.sqSub (blockD S L) = ⊥ := by
  refine C5.eq_bot_of_noCommonNormal (K := conjJoin S L) (x := x) (M₀ := M₀) (H := H) (R := S)
    m.hC52 ?_ ?_ ?_ ?_ C.hcs.eq_join.le
    (le_sup_zpowers_of_relIndex_two m.h2 m.hx m.hxS)
  · exact C5.sqSub_le_self.trans inf_le_left
  · exact C5.sqSub_le_self.trans inf_le_right
  · intro s hs
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    exact C5.conjSubgroup_sqSub_of_mem_normalizer (GCfg.S_le_N_D hs)
  · rw [← conjSubgroup_eq_iff_mem_normalizer, ← m.sqSub_K C]
    exact C5.conjSubgroup_sqSub_of_mem_normalizer
      (conjSubgroup_eq_iff_mem_normalizer.1 (m.conj_K C))

theorem D_elem : IsElemAbelian 2 (blockD S L) := by
  have h := C5.sqSub_eq_bot_iff.1 (m.sqSub_D C)
  exact C5.isElemAbelian_two_iff.mpr ⟨C5.comm_of_sq_eq_one h, h⟩

theorem Q_elem : IsElemAbelian 2 (pCoreOf 2 H) := by
  rw [C.Q_eq]
  exact B2F.isElemAbelian_sup_of_commute C.hU (m.D_elem C) fun u hu d hd => C.U_comm_D hu hd

theorem D_le_B : blockD S L ≤ baum S := by
  intro d hd
  refine ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
  exact B2F.isElemAbelian_comm (m.Q_elem C) (C.omegaOneCenter_le_pCoreOf hz) (C.D_le_Q hd)

theorem Q_le_B : pCoreOf 2 H ≤ baum S := by
  rw [C.Q_eq]
  exact sup_le C.U_le_baum (m.D_le_B C)

theorem D_inf_conj : blockD S L ⊓ conjR (blockD S L) x = ⊥ := by
  have hN := GCfg.S_le_N_D (S := S) (L := L)
  refine C5.eq_bot_of_noCommonNormal (K := conjJoin S L) (x := x) (M₀ := M₀) (H := H) (R := S)
    m.hC52 ?_ ?_ ?_ ?_ C.hcs.eq_join.le
    (le_sup_zpowers_of_relIndex_two m.h2 m.hx m.hxS)
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · intro s hs
    rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_inf,
      C5.conjSubgroup_eq_self (hN hs)]
    have := m.S_le_N_conj hN hs
    rw [← conjSubgroup_eq_iff_mem_normalizer] at this
    rw [C56.conjR_eq, this]
  · rw [← conjSubgroup_eq_iff_mem_normalizer, C56.conjR_eq, C5.conjSubgroup_inf,
      m.conj_conj_eq hN, inf_comm]

theorem B_le_sup {b : G} (hb : b ∈ baum S) :
    ∃ v ∈ conjR (C.U) x, v⁻¹ * b ∈ pCoreOf 2 H := by
  have hbS : b ∈ S := hb.1
  have hbN : b ∈ S := hbS
  have hπb : C.P.π ⟨b, hbN⟩ ∈ C.P.im (conjR C.U x) := by
    rw [m.im_V C, ← C.hB]
    exact C.P.pi_mem_im hb
  obtain ⟨v, hvV, hvπ⟩ := (C.P.mem_im).1 hπb
  have h1 : C.P.π (v⁻¹ * ⟨b, hbN⟩) = 1 := by
    rw [map_mul, map_inv, hvπ, inv_mul_cancel]
  have h2 := (C.P.hker (v⁻¹ * ⟨b, hbN⟩)).1 h1
  refine ⟨(v : G), hvV, ?_⟩
  rw [← C.hQ]
  have hvbH : (v : G)⁻¹ * b ∈ H := mul_mem (inv_mem (C.hSH (m.V_le_S C hvV))) (C.hSH hbS)
  refine ⟨hvbH, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
  have := h2 u hu
  have e : ((v⁻¹ * ⟨b, hbN⟩ : ↥S) : G) = (v : G)⁻¹ * b := rfl
  rw [e] at this
  calc u * ((v : G)⁻¹ * b) = (((v : G)⁻¹ * b) * u * ((v : G)⁻¹ * b)⁻¹) * ((v : G)⁻¹ * b) := by
        rw [this]
    _ = ((v : G)⁻¹ * b) * u := by group

theorem B_eq_sup : baum S = conjR (C.U) x ⊔ pCoreOf 2 H := by
  apply le_antisymm
  · intro b hb
    obtain ⟨v, hv, hq⟩ := m.B_le_sup C hb
    have : b = v * (v⁻¹ * b) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hq)
  · exact sup_le (m.V_le_B C) (m.Q_le_B C)

theorem B_eq : baum S = blockD S L ⊔ C.U ⊔ conjR (C.U) x := by
  rw [m.B_eq_sup C, C.Q_eq, sup_comm (C.U), sup_comm]

end GMate

end CFSG.Quasithin.YG.AppD
