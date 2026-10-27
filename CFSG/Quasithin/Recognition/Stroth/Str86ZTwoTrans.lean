module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound
public import CFSG.Quasithin.Recognition.Stroth.F112U3Vertex
public import CFSG.Quasithin.Recognition.Stroth.Y9Transport
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_mul_inv_mem_of_relIndex {H B S Q : Subgroup G} (hBH : B ≤ H) (hSB : S ≤ B)
    (hQS : Q ≤ S) (hidx : B.relIndex H = Q.relIndex S + 1)
    (hstab : ∀ g ∈ H, g ∉ B → S ⊓ (MulAut.conj g • B) ≤ Q)
    {g g' : G} (hg : g ∈ H) (hgB : g ∉ B) (hg' : g' ∈ H) (hg'B : g' ∉ B) :
    ∃ s ∈ S, (s * g)⁻¹ * g' ∈ B := by
  classical
  let base : G ⧸ B := (QuotientGroup.mk (1 : G) : G ⧸ B)
  let x : G ⧸ B := (QuotientGroup.mk g : G ⧸ B)
  let C : Set (G ⧸ B) := MulAction.orbit (↥H) base
  let C' : Set (G ⧸ B) := C \ {base}
  let O : Set (G ⧸ B) := MulAction.orbit (↥S) x
  have hstabG : MulAction.stabilizer G base = B := by
    change MulAction.stabilizer G ((1 : G) : G ⧸ B) = B
    rw [MulAction.stabilizer_quotient]
  have hstabH : MulAction.stabilizer (↥H) base = B.subgroupOf H := by
    rw [← MulAction.stabilizer_subgroupOf H base, hstabG]
  have hnotbase : ∀ h ∈ H, h ∉ B → (QuotientGroup.mk h : G ⧸ B) ≠ base := by
    intro h _ hhB heq
    apply hhB
    have hmem : h⁻¹ * 1 ∈ B := QuotientGroup.eq.mp heq
    have hh' : h⁻¹ ∈ B := by simpa using hmem
    simpa using B.inv_mem hh'
  have hxne : x ≠ base := hnotbase g hg hgB
  have hOC' : O ⊆ C' := by
    intro y hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨s, rfl⟩ := hy
    have hsg : (s : G) * g ∈ H := H.mul_mem (hBH (hSB s.2)) hg
    have hyx : (s : G) • x = (QuotientGroup.mk ((s : G) * g) : G ⧸ B) := by
      rw [show x = (QuotientGroup.mk g : G ⧸ B) from rfl,
        MulAction.Quotient.smul_mk B (s : G) g]
      simp
    have hyC : (s : G) • x ∈ C := by
      rw [hyx]
      exact MulAction.mem_orbit_iff.mpr ⟨⟨(s : G) * g, hsg⟩, by
        rw [show base = (QuotientGroup.mk (1 : G) : G ⧸ B) from rfl, Subgroup.smul_def,
          MulAction.Quotient.smul_mk B ((s : G) * g) (1 : G)]
        simp⟩
    refine ⟨hyC, ?_⟩
    intro h
    have hcos : (QuotientGroup.mk ((s : G) * g) : G ⧸ B) = base := by
      rw [← hyx]
      exact h
    have hmem : ((s : G) * g)⁻¹ * 1 ∈ B := QuotientGroup.eq.mp hcos
    have hsgB : (s : G) * g ∈ B := by
      have : ((s : G) * g)⁻¹ ∈ B := by simpa using hmem
      simpa using B.inv_mem this
    have hsB : (s : G) ∈ B := hSB s.2
    have hgB' : g ∈ B := by
      have he : g = (s : G)⁻¹ * ((s : G) * g) := by group
      rw [he]
      exact B.mul_mem (B.inv_mem hsB) hsgB
    exact hgB hgB'
  have hxC' : x ∈ C' := by
    refine ⟨?_, hxne⟩
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, by
      rw [show base = (QuotientGroup.mk (1 : G) : G ⧸ B) from rfl, Subgroup.smul_def,
        MulAction.Quotient.smul_mk B g (1 : G)]
      simp
      rfl⟩
  have hstab_eq : MulAction.stabilizer (↥S) x = (MulAut.conj g • B).subgroupOf S := by
    ext s
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have hsdef : (s : ↥S) • x = (s : G) • x := Subgroup.smul_def s x
    rw [hsdef]
    have hxs : (s : G) • x = (QuotientGroup.mk ((s : G) * g) : G ⧸ B) := by
      rw [show x = (QuotientGroup.mk g : G ⧸ B) from rfl,
        MulAction.Quotient.smul_mk B (s : G) g]
      simp
    rw [hxs]
    constructor
    · intro h
      have hmem : ((s : G) * g)⁻¹ * g ∈ B := QuotientGroup.eq.mp h
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hinv : (MulAut.conj g)⁻¹ • (s : G) = g⁻¹ * (s : G) * g := by
        rw [MulAut.smul_def, MulAut.conj_inv_apply]
      rw [hinv]
      have heq : ((s : G) * g)⁻¹ * g = (g⁻¹ * (s : G) * g)⁻¹ := by group
      rw [heq] at hmem
      simpa using B.inv_mem hmem
    · intro h
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
      have hinv : (MulAut.conj g)⁻¹ • (s : G) = g⁻¹ * (s : G) * g := by
        rw [MulAut.smul_def, MulAut.conj_inv_apply]
      rw [hinv] at h
      rw [show x = (QuotientGroup.mk g : G ⧸ B) from rfl]
      apply QuotientGroup.eq.mpr
      have heq : ((s : G) * g)⁻¹ * g = (g⁻¹ * (s : G) * g)⁻¹ := by group
      rw [heq]
      simpa using B.inv_mem h
  have hstabindex : (MulAction.stabilizer (↥S) x).index =
      (S ⊓ (MulAut.conj g • B)).relIndex S := by
    rw [hstab_eq]
    have h1 : ((MulAut.conj g • B).subgroupOf S).index = (MulAut.conj g • B).relIndex S := rfl
    rw [h1, inf_comm, Subgroup.inf_relIndex_right]
  have hOcard : Nat.card O = (MulAction.stabilizer (↥S) x).index := by
    rw [Nat.card_coe_set_eq, MulAction.index_stabilizer]
  have hbaseC : base ∈ C := MulAction.mem_orbit_iff.mpr ⟨1, by simp⟩
  have hCcard : Nat.card C = B.relIndex H := by
    have h1 : (MulAction.stabilizer (↥H) base).index = Nat.card C := by
      rw [Nat.card_coe_set_eq, MulAction.index_stabilizer]
    rw [← h1, hstabH]
    rfl
  have hC'card : Nat.card C' = Q.relIndex S := by
    have h := Set.ncard_sdiff_singleton_add_one hbaseC
    rw [← Nat.card_coe_set_eq C', ← Nat.card_coe_set_eq C] at h
    rw [hCcard, hidx] at h
    omega
  have hle' : C'.ncard ≤ O.ncard := by
    rw [← Nat.card_coe_set_eq C', ← Nat.card_coe_set_eq O, hC'card, hOcard, hstabindex]
    exact Subgroup.relIndex_le_of_le_left (hstab g hg hgB) (D15Proof.relIndex_ne_zero _ _)
  have heq : O = C' := Set.eq_of_subset_of_ncard_le hOC' hle'
  have hx'C' : (QuotientGroup.mk g' : G ⧸ B) ∈ C' := by
    refine ⟨?_, hnotbase g' hg' hg'B⟩
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g', hg'⟩, by
      rw [show base = (QuotientGroup.mk (1 : G) : G ⧸ B) from rfl, Subgroup.smul_def,
        MulAction.Quotient.smul_mk B g' (1 : G)]
      simp⟩
  have hx'O : (QuotientGroup.mk g' : G ⧸ B) ∈ O := by
    rw [heq]
    exact hx'C'
  rw [MulAction.mem_orbit_iff] at hx'O
  obtain ⟨s, hs⟩ := hx'O
  refine ⟨(s : G), s.2, ?_⟩
  have hcos : (QuotientGroup.mk ((s : G) * g) : G ⧸ B) =
      (QuotientGroup.mk g' : G ⧸ B) := by
    rw [← hs, Subgroup.smul_def]
    rw [show x = (QuotientGroup.mk g : G ⧸ B) from rfl,
      MulAction.Quotient.smul_mk B (s : G) g]
    simp
  exact QuotientGroup.eq.mp hcos

theorem str86_u3B_inf_conj_le_q1 {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {g : G} (hg : g ∈ L1 ⊔ S) (hgB : g ∉ bigB L1 L2 S) :
    S ⊓ (MulAut.conj g • (bigB L1 L2 S ⊓ (L1 ⊔ S))) ≤ Q1 L1 L2 S := by
  classical
  set B : Subgroup G := bigB L1 L2 S ⊓ (L1 ⊔ S) with hB
  have hSB_le : S ≤ B := le_inf le_sup_right le_sup_right
  have hBP1 : B ≤ P1 L1 L2 S := by
    rw [hB]
    exact (inf_le_right : _ ≤ L1 ⊔ S).trans
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
  have hSylB : IsSylowTwoOf S B :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF.toW) hSB_le hBP1
  have hBN : B ≤ Subgroup.normalizer (S : Set G) :=
    (inf_le_left : B ≤ bigB L1 L2 S).trans hSB
  have hSylgB : IsSylowTwoOf (MulAut.conj g • S) (MulAut.conj g • B) :=
    F7.isSylowTwoOf_conj hSylB g
  have hgBN : MulAut.conj g • B ≤ Subgroup.normalizer (MulAut.conj g • S : Set G) := by
    let f : G →* G := MulDistribMulAction.toMonoidHom G (MulAut.conj g)
    have h := (Subgroup.map_mono (f := f) hBN).trans (Subgroup.le_normalizer_map (H := S) f)
    simpa [f, CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul] using h
  have hle_gSB : MulAut.conj g • S ≤ MulAut.conj g • B :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr hSB_le
  have hNnormal : ((MulAut.conj g • S).subgroupOf (MulAut.conj g • B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle_gSB).mpr hgBN
  have hT2 : IsPGroup 2 ↥(S ⊓ (MulAut.conj g • B)) :=
    hF.1.h1.pgroup.to_le inf_le_left
  have hle : S ⊓ (MulAut.conj g • B) ≤ MulAut.conj g • S :=
    CFSG.Quasithin.Stroth.le_of_isSylowTwoOf_normal hSylgB hNnormal inf_le_right hT2
  have h1 : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1) :=
    Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩)
  have hbig : g ∈ L1 ⊔ bigB L1 L2 S :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) hg
  have hTI := f112_sylow_inf_conj_eq_pCoreOf_left hF.toW hSB h1 hbig hgB
  have hfinal : S ⊓ (MulAut.conj g • B) ≤ Q1 L1 L2 S := by
    calc S ⊓ (MulAut.conj g • B) ≤ S ⊓ (MulAut.conj g • S) := le_inf inf_le_left hle
      _ = Q1 L1 L2 S := hTI
  rwa [hB] at hfinal

theorem str86_relIndex_u3B {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    (bigB L1 L2 S ⊓ (L1 ⊔ S)).relIndex (L1 ⊔ S) = (2 ^ k) ^ 3 + 1 := by
  classical
  have hsup : (L1 ⊔ S) ⊔ bigB L1 L2 S = L1 ⊔ bigB L1 L2 S := by
    rw [sup_assoc, show S ⊔ bigB L1 L2 S = bigB L1 L2 S from
      sup_eq_right.mpr (le_sup_right : S ≤ bigB L1 L2 S)]
  have hnorm : bigB L1 L2 S ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (bigB_le_normalizer_of_hyp111 hF.1) hSB
  have hrel := F112W.relIndex_sup_eq_relIndex_inf (N := L1 ⊔ S) (B := bigB L1 L2 S) hnorm
  rw [hsup] at hrel
  calc (bigB L1 L2 S ⊓ (L1 ⊔ S)).relIndex (L1 ⊔ S)
      = ((L1 ⊔ S) ⊓ bigB L1 L2 S).relIndex (L1 ⊔ S) := by rw [inf_comm]
    _ = (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) := hrel.symm
    _ = (2 ^ k) ^ 3 + 1 := f112_relIndex_bigB_of_u3 hF hk hFc hU3

theorem exists_isChiefSeriesFrom_u3X1 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) :
    ∃ c, IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c := by
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hXle : u3X1 L1 L2 S ≤ L1 ⊔ S :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans (hQ1S.trans le_sup_right)
  refine D15Proof.exists_isChiefSeriesFrom _ ⟨le_rfl, ?_⟩
  intro g hg x hx
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF hg) x).mp hx

theorem str86_u3Y_conj_transitive_of_chief
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c)
    {g g' : G} (hg : g ∈ L1 ⊔ S) (hgB : g ∉ bigB L1 L2 S)
    (hg' : g' ∈ L1 ⊔ S) (hg'B : g' ∉ bigB L1 L2 S) :
    ∃ s ∈ S, MulAut.conj (s * g) • u3Y L1 L2 S = MulAut.conj g' • u3Y L1 L2 S := by
  classical
  set B : Subgroup G := bigB L1 L2 S ⊓ (L1 ⊔ S) with hB
  have hBH : B ≤ L1 ⊔ S := inf_le_right
  have hSB_le : S ≤ B := le_inf le_sup_right le_sup_right
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hidx : B.relIndex (L1 ⊔ S) = (Q1 L1 L2 S).relIndex S + 1 := by
    rw [hB, str86_relIndex_u3B hF hSB hk hFc hU3,
      str86_relIndex_q1_s hF hSB hk hFc hU3]
  have hstab : ∀ g ∈ L1 ⊔ S, g ∉ B → S ⊓ (MulAut.conj g • B) ≤ Q1 L1 L2 S := by
    intro g hg hgB
    have hgbig : g ∉ bigB L1 L2 S := fun h => hgB (Subgroup.mem_inf.mpr ⟨h, hg⟩)
    have h := str86_u3B_inf_conj_le_q1 hF hSB hk hFc hU3 hg hgbig
    rwa [← hB] at h
  have hgB' : g ∉ B := fun h => hgB (Subgroup.mem_inf.mp h).1
  have hg'B' : g' ∉ B := fun h => hg'B (Subgroup.mem_inf.mp h).1
  obtain ⟨s, hsS, hsmem⟩ := exists_mem_mul_inv_mem_of_relIndex hBH hSB_le hQ1S hidx
    hstab hg hgB' hg' hg'B'
  refine ⟨s, hsS, ?_⟩
  set h : G := (s * g)⁻¹ * g' with hh
  have hhH : h ∈ L1 ⊔ S := by
    refine (L1 ⊔ S).mul_mem ((L1 ⊔ S).inv_mem ?_) hg'
    exact (L1 ⊔ S).mul_mem ((le_sup_right : S ≤ L1 ⊔ S) hsS) hg
  have hhB : h ∈ bigB L1 L2 S := (Subgroup.mem_inf.mp hsmem).1
  have hconjY : MulAut.conj h • u3Y L1 L2 S = u3Y L1 L2 S := by
    have hmemBH : h ∈ bigB L1 L2 S ⊓ (L1 ⊔ S) := Subgroup.mem_inf.mpr ⟨hhB, hhH⟩
    exact (str86_u3Y_conj_eq_iff hF hSB hk hFc hU3 hn hL2 hZQ hser hhH).mpr hmemBH
  have hconj_mul_smul : ∀ a b : G,
      MulAut.conj (a * b) • u3Y L1 L2 S =
        MulAut.conj a • (MulAut.conj b • u3Y L1 L2 S) := by
    intro a b
    rw [map_mul, mul_smul]
  calc MulAut.conj (s * g) • u3Y L1 L2 S
      = MulAut.conj (s * g) • (MulAut.conj h • u3Y L1 L2 S) := by rw [hconjY]
    _ = MulAut.conj ((s * g) * h) • u3Y L1 L2 S := (hconj_mul_smul (s * g) h).symm
    _ = MulAut.conj g' • u3Y L1 L2 S := by
        have : (s * g) * h = g' := by
          rw [hh]
          group
        rw [this]

theorem isPGroup_imageOTwoQuot_of_isSylow {H S : Subgroup G} (hS : IsSylowTwoOf S H) :
    IsPGroup 2 ↥(imageOTwoQuot H S) := by
  let N : Subgroup ↥H := CFSG.Open.pCore 2 ↥H
  let f : ↥H →* OTwoQuot H := QuotientGroup.mk' N
  exact (A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1).map f

theorem not_two_dvd_index_imageOTwoQuot {H S : Subgroup G} (hS : IsSylowTwoOf S H) :
    ¬ 2 ∣ (imageOTwoQuot H S).index := by
  let N : Subgroup ↥H := CFSG.Open.pCore 2 ↥H
  let f : ↥H →* OTwoQuot H := QuotientGroup.mk' N
  change ¬ 2 ∣ (Subgroup.map f (S.subgroupOf H)).index
  have hmap := Subgroup.index_map (H := S.subgroupOf H) (f := f)
  have hker : f.ker = N := QuotientGroup.ker_mk' N
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hNle : N ≤ S.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact F7.isSylowTwoOf_pCoreOf_le hS ((F1.mem_pCore_iff_coe x).mp hx)
  have hsup : S.subgroupOf H ⊔ N = S.subgroupOf H := sup_eq_left.mpr hNle
  rw [hker, hrange, Subgroup.index_top, mul_one, hsup] at hmap
  rw [hmap]
  exact hS.2.2

private theorem str86_sq_mem_q2_aux {L1 L2 S H2 : Subgroup G}
    {n : ℕ} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hH2 : H2 = L2 ⊔ Q2 L1 L2 S) {s : G} (hs : s ∈ S) : s * s ∈ Q2 L1 L2 S := by
  classical
  have hq : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
  have hcoreH2 : pCoreOf 2 H2 = Q2 L1 L2 S := by
    calc pCoreOf 2 H2 = pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) := by rw [hH2]
      _ = pCoreOf 2 (L2 ⊔ Q1 L2 L1 S) := by rw [hq]
      _ = Q1 L2 L1 S := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      _ = Q2 L1 L2 S := hq
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩))
  have hS_le_H2 : S ≤ H2 := by
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := by
          apply sup_le
          · exact inf_le_right.trans le_sup_left
          · exact le_sup_right
      _ = H2 := hH2.symm
  have hH2_le_P2 : H2 ≤ P2 L1 L2 S := by
    calc H2 = L2 ⊔ Q2 L1 L2 S := hH2
      _ ≤ P2 L1 L2 S := by
          apply sup_le le_sup_left
          exact pCoreOf_le 2 (P2 L1 L2 S)
  have hSylP2 : IsSylowTwoOf S (P2 L1 L2 S) := f112_isSylowTwoOf_P2 hF
  have hSylH2 : IsSylowTwoOf S H2 := F7.isSylowTwoOf_mono_right hSylP2 hS_le_H2 hH2_le_P2
  let T : Subgroup (OTwoQuot H2) := imageOTwoQuot H2 S
  have hT2 : IsPGroup 2 ↥T := isPGroup_imageOTwoQuot_of_isSylow hSylH2
  have hTindex : ¬ 2 ∣ T.index := not_two_dvd_index_imageOTwoQuot hSylH2
  let P : Sylow 2 (OTwoQuot H2) := hT2.toSylow hTindex
  have hPcoe : (P : Subgroup (OTwoQuot H2)) = T := IsPGroup.toSylow_coe hT2 hTindex
  let e : OTwoQuot H2 ≃* OTwoQuot L2 := by
    have hH2' : H2 = L2 ⊔ Q1 L2 L1 S := by
      calc H2 = L2 ⊔ Q2 L1 L2 S := hH2
        _ = L2 ⊔ Q1 L2 L1 S := by rw [hq]
    rw [hH2']
    exact oTwoQuotSupEquiv (L1 := L2) (L2 := L1) (S := S) hF.1.symm
  let P' : Sylow 2 (OTwoQuot L2) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP'coe : (P' : Subgroup (OTwoQuot L2)) = T.map e.toMonoidHom := by
    rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) (hf := e.surjective) (P := P), hPcoe]
  have hsq := (l2Sylow_sq_mem (H := L2) hn hL2 P').1
  let x : ↥H2 := ⟨s, hSylH2.1 hs⟩
  have hxT : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H2) x ∈ T :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hex : e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H2) x) ∈
      (P' : Subgroup (OTwoQuot L2)) := by
    rw [hP'coe]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hxT
  have hsquare : e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H2) x) *
      e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H2) x) = 1 := hsq _ hex
  have hsquare' : e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H2) (x * x)) = 1 := by
    simpa [map_mul] using hsquare
  have hf1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H2) (x * x) = 1 := by
    apply e.injective
    rw [hsquare']
    exact (map_one e).symm
  have hmemN : (x * x : ↥H2) ∈ CFSG.Open.pCore 2 ↥H2 :=
    (QuotientGroup.eq_one_iff (x * x)).mp hf1
  have hmemP : (s * s : G) ∈ pCoreOf 2 H2 := by
    have h' := (F1.mem_pCore_iff_coe (x * x)).mp hmemN
    simpa [x] using h'
  rwa [hcoreH2] at hmemP

theorem str86_sq_mem_q2 {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {s : G} (hs : s ∈ S) :
    s * s ∈ Q2 L1 L2 S :=
  str86_sq_mem_q2_aux (H2 := L2 ⊔ Q2 L1 L2 S) hF hSB hn hL2 rfl hs

theorem str86_commutator_mem_q2 {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {a b : G} (ha : a ∈ S) (hb : b ∈ S) :
    a * b * a⁻¹ * b⁻¹ ∈ Q2 L1 L2 S := by
  classical
  let N : Subgroup ↥S := (Q2 L1 L2 S).subgroupOf S
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ2S).mpr le_normalizer_q2_of_sylow
  have hExp : ∀ x : ↥S ⧸ N, x * x = 1 := by
    intro x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    change ((s * s : ↥S) : ↥S ⧸ N) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (str86_sq_mem_q2 hF.toW hSB hn hL2 s.2)
  have hComm : ∀ x y : ↥S ⧸ N, x * y = y * x := by
    intro x y
    have hx : x * x = 1 := hExp x
    have hy : y * y = 1 := hExp y
    have hxy : (x * y) * (x * y) = 1 := hExp (x * y)
    have h1 : y * x * y = x := by
      have hcongr := congrArg (fun z => x * z) hxy
      calc y * x * y = 1 * (y * x * y) := by rw [one_mul]
        _ = (x * x) * (y * x * y) := by rw [hx]
        _ = x * ((x * y) * (x * y)) := by group
        _ = x * 1 := hcongr
        _ = x := mul_one x
    have h2 : y * x = x * y := by
      calc y * x = y * x * 1 := by rw [mul_one]
        _ = y * x * (y * y) := by rw [hy]
        _ = (y * x * y) * y := by group
        _ = x * y := by rw [h1]
    exact h2.symm
  have hq : (QuotientGroup.mk (⟨a, ha⟩ : ↥S) : ↥S ⧸ N) * QuotientGroup.mk ⟨b, hb⟩ =
      QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩ := hComm _ _
  have hmemN : ((⟨a, ha⟩ : ↥S) * ⟨b, hb⟩) * (⟨b, hb⟩ * ⟨a, ha⟩)⁻¹ ∈ N := by
    simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).mp hq
  have h' := Subgroup.mem_subgroupOf.mp hmemN
  simpa [mul_assoc] using h'

theorem str86_le_normalizer_of_q2_le {L1 L2 S R : Subgroup G}
    (hQR : Q2 L1 L2 S ≤ R) (hRS : R ≤ S)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ Q2 L1 L2 S) :
    S ≤ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro s hs r hr
  have hcomm_sr : s * r * s⁻¹ * r⁻¹ ∈ Q2 L1 L2 S := hcomm s hs r (hRS hr)
  have hmem : s * r * s⁻¹ * r⁻¹ ∈ R := hQR hcomm_sr
  have he : s * r * s⁻¹ = (s * r * s⁻¹ * r⁻¹) * r := by group
  rw [he]
  exact R.mul_mem hmem hr

theorem str86_u3Y_conj_sup_q2_of_chief
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c)
    {g : G} (hg : g ∈ L1 ⊔ S) (hgB : g ∉ bigB L1 L2 S) :
    MulAut.conj g • u3Y L1 L2 S ⊔ Q2 L1 L2 S = S := by
  classical
  let Y : Subgroup G := u3Y L1 L2 S
  let R : Subgroup G := MulAut.conj g • Y ⊔ Q2 L1 L2 S
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hRS : R ≤ S := by
    apply sup_le
    · exact (str86_u3Y_conj_le_q1 hg).trans hQ1S
    · exact hQ2S
  have hYQ2 : Y ≤ Q2 L1 L2 S :=
    (u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S)).trans (omegaOneCenterOf_le (Q2 L1 L2 S))
  have hYR : Y ≤ R := hYQ2.trans le_sup_right
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ Q2 L1 L2 S :=
    fun a ha b hb => str86_commutator_mem_q2 hF hSB hn hL2 ha hb
  have hRnorm : S ≤ Subgroup.normalizer (R : Set G) :=
    str86_le_normalizer_of_q2_le (L1 := L1) (L2 := L2) (S := S) (R := R)
      le_sup_right hRS hcomm
  have hconj_mul_smul : ∀ a b : G, MulAut.conj (a * b) • Y =
      MulAut.conj a • (MulAut.conj b • Y) := by
    intro a b
    rw [map_mul, mul_smul]
  have hXle : u3X1 L1 L2 S ≤ R := by
    rw [u3X1]
    refine conjClosure_le ?_
    intro l hl y hy
    have hlH : l ∈ L1 ⊔ S := (le_sup_left : L1 ≤ L1 ⊔ S) hl
    have hyl : MulAut.conj l • y ∈ MulAut.conj l • Y :=
      Subgroup.smul_mem_pointwise_smul y (MulAut.conj l) Y hy
    have hly : MulAut.conj l • y = l * y * l⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_apply]
    have hgoal : MulAut.conj l • y ∈ R := by
      by_cases hlB : l ∈ bigB L1 L2 S
      · have hlBH : l ∈ bigB L1 L2 S ⊓ (L1 ⊔ S) := Subgroup.mem_inf.mpr ⟨hlB, hlH⟩
        have hconjY : MulAut.conj l • Y = Y :=
          (str86_u3Y_conj_eq_iff hF hSB hk hFc hU3 hn hL2 hZQ hser hlH).mpr hlBH
        have hmem : MulAut.conj l • y ∈ Y := by
          rw [← hconjY]
          exact hyl
        exact hYR hmem
      · obtain ⟨s, hsS, hEq⟩ :=
          str86_u3Y_conj_transitive_of_chief hF hSB hk hFc hU3 hn hL2 hZQ hser
            hg hgB hlH hlB
        have hsN : s ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
          le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S) hsS
        have hQ2fix : MulAut.conj s • Q2 L1 L2 S = Q2 L1 L2 S := by
          rw [mulAut_conj_smul_eq_conjAct]
          exact Subgroup.conjAct_pointwise_smul_eq_self hsN
        have hRs : MulAut.conj s • R = MulAut.conj (s * g) • Y ⊔ Q2 L1 L2 S := by
          calc MulAut.conj s • R
              = MulAut.conj s • (MulAut.conj g • Y ⊔ Q2 L1 L2 S) := rfl
            _ = MulAut.conj s • (MulAut.conj g • Y) ⊔ MulAut.conj s • Q2 L1 L2 S := by
                rw [Subgroup.smul_sup]
            _ = MulAut.conj (s * g) • Y ⊔ Q2 L1 L2 S := by
                rw [← hconj_mul_smul s g, hQ2fix]
        have hRfix : MulAut.conj s • R = R := by
          rw [mulAut_conj_smul_eq_conjAct]
          exact Subgroup.conjAct_pointwise_smul_eq_self (hRnorm hsS)
        have hReq : MulAut.conj (s * g) • Y ⊔ Q2 L1 L2 S = R := hRs ▸ hRfix
        have hmem : MulAut.conj l • y ∈ R := by
          have hyl' : MulAut.conj l • y ∈ MulAut.conj (s * g) • Y := by
            rwa [← hEq] at hyl
          rw [← hReq]
          exact Subgroup.mem_sup_left hyl'
        exact hmem
    simpa [hly] using hgoal
  have hSleR : S ≤ R := by
    rw [← str86_u3X1_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hser]
    exact sup_le hXle le_sup_right
  exact le_antisymm hRS hSleR

theorem str86_u3Y_conj_sup_q2
    {L1 L2 S : Subgroup G}
    {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {g : G} (hg : g ∈ L1 ⊔ S) (hgB : g ∉ bigB L1 L2 S) :
    MulAut.conj g • u3Y L1 L2 S ⊔ Q2 L1 L2 S = S := by
  obtain ⟨c, hser⟩ := exists_isChiefSeriesFrom_u3X1 (L1 := L1) (L2 := L2) (S := S) hF
  exact str86_u3Y_conj_sup_q2_of_chief hF hSB hk hFc hU3 hn hL2 hZQ hser hg hgB
