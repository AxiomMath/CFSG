module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even8

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open Equiv

namespace ThreeOne

private theorem isSylowTwoOf_D :
    IsSylowTwoOf Even8.D (alternatingGroup (Fin 8)) := by
  refine ⟨Even8.D_le,
    Even8.isSylow_D.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe Even8.D_le), ?_⟩
  have hidx : ((Even8.D.subgroupOf (alternatingGroup (Fin 8))).subgroupOf
      (⊤ : Subgroup ↥(alternatingGroup (Fin 8)))).index =
      (Even8.D.subgroupOf (alternatingGroup (Fin 8))).index :=
    Subgroup.relIndex_top_right _
  intro hdvd
  exact Even8.isSylow_D.2.2 (hidx.symm ▸ hdvd)

private theorem cert_sizes :
    Even8.cert.sizes = [64, 192, 192, 192, 576, 1344, 1344, 20160] := rfl

private theorem pCoreOf_subgroupOf {G : Type*} [Group G] {A H : Subgroup G} (hHA : H ≤ A) :
    pCoreOf 2 H = (pCoreOf 2 (H.subgroupOf A)).map A.subtype := by
  let Y : Subgroup ↥A := H.subgroupOf A
  let e : ↥Y ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHA
  have hmap : (pCore 2 ↥Y).map e.toMonoidHom = pCore 2 ↥H := CFSG.pCore_map_iso 2 e
  have hcomp : H.subtype.comp e.toMonoidHom = A.subtype.comp Y.subtype := by
    ext y
    rfl
  calc pCoreOf 2 H = (pCore 2 ↥H).map H.subtype := rfl
    _ = ((pCore 2 ↥Y).map e.toMonoidHom).map H.subtype := by rw [hmap]
    _ = (pCore 2 ↥Y).map (H.subtype.comp e.toMonoidHom) := by rw [Subgroup.map_map]
    _ = (pCore 2 ↥Y).map (A.subtype.comp Y.subtype) := by rw [hcomp]
    _ = ((pCore 2 ↥Y).map Y.subtype).map A.subtype := by rw [Subgroup.map_map]
    _ = (pCoreOf 2 Y).map A.subtype := rfl

private theorem charTwo_of_subgroupOf {G : Type*} [Group G] {A H : Subgroup G} (hHA : H ≤ A)
    (h : CharTwo (H.subgroupOf A)) : CharTwo H := by
  have hQeq := pCoreOf_subgroupOf hHA
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxC⟩ := hx
  rw [hQeq]
  refine Subgroup.mem_map.mpr ⟨⟨x, hHA hxH⟩, ?_, rfl⟩
  refine h (Subgroup.mem_inf.mpr ⟨hxH, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  apply Subtype.ext
  have hzG : (z : G) ∈ pCoreOf 2 H := by
    rw [hQeq]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp hxC (z : G) hzG

private theorem conjSub_centralizer {G : Type*} [Group G] (g : G) (Q : Subgroup G) :
    B6.conjSub g (Subgroup.centralizer (Q : Set G)) =
      Subgroup.centralizer (B6.conjSub g Q : Set G) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ Q := B6.mem_conjSub.mp hy
    have key := h (g⁻¹ * y * g) hy'
    have h1 : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    have h2 : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    rw [h1, h2, key]
  · intro h y hy
    have hy' : g * y * g⁻¹ ∈ B6.conjSub g Q := by
      rw [B6.mem_conjSub]
      have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [this]
    have key := h (g * y * g⁻¹) hy'
    have h1 : y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
    have h2 : (g⁻¹ * x * g) * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
    rw [h1, h2, key]

private theorem pCoreOf_spec (K : Subgroup (Perm (Fin 8))) (hchar : CharTwo K) :
    pCoreOf 2 K ≤ K ∧ ((pCoreOf 2 K).subgroupOf K).Normal ∧ IsPGroup 2 (pCoreOf 2 K) ∧
      K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set (Perm (Fin 8))) ≤ pCoreOf 2 K := by
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K, ?_, ?_, hchar⟩
  · have hQ : (pCoreOf 2 K).subgroupOf K = pCore 2 K := by
      rw [show (pCoreOf 2 K).subgroupOf K =
        ((pCore 2 ↥K).map K.subtype).comap K.subtype from rfl]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective (pCore 2 K)
    rw [hQ]
    infer_instance
  · exact (CFSG.pCore_isPGroup (G := ↥K) (p := 2)).map K.subtype

private theorem conjSub_spec {g : Perm (Fin 8)} {K Q : Subgroup (Perm (Fin 8))}
    (hQ : Q ≤ K) (hnorm : (Q.subgroupOf K).Normal) (h2 : IsPGroup 2 Q)
    (hcent : K ⊓ Subgroup.centralizer (Q : Set (Perm (Fin 8))) ≤ Q) :
    B6.conjSub g Q ≤ B6.conjSub g K ∧
      ((B6.conjSub g Q).subgroupOf (B6.conjSub g K)).Normal ∧
      IsPGroup 2 (B6.conjSub g Q) ∧
      B6.conjSub g K ⊓ Subgroup.centralizer (B6.conjSub g Q : Set (Perm (Fin 8))) ≤
        B6.conjSub g Q := by
  have hQ' : B6.conjSub g Q ≤ B6.conjSub g K := (B6.conjSub g).le_iff_le.mpr hQ
  refine ⟨hQ', ?_, h2.map (MulAut.conj g).toMonoidHom, ?_⟩
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQ').mpr ?_
    have hk : K ≤ Subgroup.normalizer (Q : Set (Perm (Fin 8))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQ).mp hnorm
    have hnormalizer : B6.conjSub g (Subgroup.normalizer (Q : Set (Perm (Fin 8)))) =
        Subgroup.normalizer (B6.conjSub g Q : Set (Perm (Fin 8))) := by
      simpa only [B6.conjSub, MulEquiv.coe_mapSubgroup] using
        Subgroup.map_normalizer_eq_of_bijective Q (MulAut.conj g).bijective
    rw [← hnormalizer]
    exact (B6.conjSub g).le_iff_le.mpr hk
  · have hmapinf : B6.conjSub g K ⊓
        Subgroup.centralizer (B6.conjSub g Q : Set (Perm (Fin 8))) =
        B6.conjSub g (K ⊓ Subgroup.centralizer (Q : Set (Perm (Fin 8)))) := by
      rw [← conjSub_centralizer g Q]
      exact (OrderIso.map_inf (B6.conjSub g) K
        (Subgroup.centralizer (Q : Set (Perm (Fin 8))))).symm
    rw [hmapinf]
    exact (B6.conjSub g).le_iff_le.mpr hcent

theorem card_mem_of_le_alternatingGroup_eight
    {S K : Subgroup (Perm (Fin 8))} (hK : K ≤ alternatingGroup (Fin 8))
    (hS : IsSylowIn 2 S (alternatingGroup (Fin 8))) (hSK : S ≤ K) :
    Nat.card K = 64 ∨ Nat.card K = 192 ∨ Nat.card K = 576 ∨ Nat.card K = 1344 ∨
      Nat.card K = 20160 := by
  obtain ⟨g, hgA, hgS⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_D hS
  set h : Perm (Fin 8) := g⁻¹ with hh
  have hhA : h ∈ alternatingGroup (Fin 8) := by
    rw [hh]
    exact (alternatingGroup (Fin 8)).inv_mem hgA
  have hhD : Even8.D = B6.conjSub h S := by
    have : B6.conjSub h S = Even8.D := by
      rw [hgS, hh, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
    exact this.symm
  set K' : Subgroup (Perm (Fin 8)) := B6.conjSub h K with hK'def
  have hK'A : K' ≤ alternatingGroup (Fin 8) := by
    have hfix : B6.conjSub h (alternatingGroup (Fin 8)) = alternatingGroup (Fin 8) :=
      B6.conjSub_eq_self (Subgroup.le_normalizer hhA)
    calc K' = B6.conjSub h K := hK'def
      _ ≤ B6.conjSub h (alternatingGroup (Fin 8)) := (B6.conjSub h).le_iff_le.mpr hK
      _ = alternatingGroup (Fin 8) := hfix
  have hDK' : Even8.D ≤ K' := by
    calc Even8.D = B6.conjSub h S := hhD
      _ ≤ B6.conjSub h K := (B6.conjSub h).le_iff_le.mpr hSK
      _ = K' := hK'def.symm
  have hcardK' : Nat.card K' = Nat.card K := by
    show Nat.card (B6.conjSub h K) = Nat.card K
    simpa only [B6.conjSub, MulEquiv.coe_mapSubgroup] using
      Subgroup.card_mapSubgroup (H := K) (MulAut.conj h)
  have hTY : Subgroup.closure {g | g ∈ Even8.cert.tGens} ≤ K' := by
    have ht : Even8.cert.tGens = Even8.tGens := rfl
    rw [ht]
    exact hDK'
  have hYM : K' ≤ Subgroup.closure {g | g ∈ Even8.cert.mGens} := by
    have hm : Even8.cert.mGens = Even8.mGens := rfl
    rw [hm, Even8.closure_mGens]
    exact hK'A
  obtain ⟨L, hL, hLK'⟩ := Even8.cert.overgroups (rawIsEnc 8) Even8.cert_check K' hTY hYM
  have hcl := Even8.cert.closedOK_of_check Even8.cert_check
  have hsz := Even8.cert.sizesOK_of_check Even8.cert_check
  have hmem := Even8.cert.card_member (rawIsEnc 8) hcl hsz L hL
  rw [← hLK'] at hmem
  rw [← hcardK']
  rw [cert_sizes] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  tauto

theorem exists_le_inf_centralizer_le
    {S K : Subgroup (Perm (Fin 8))} (hK : K ≤ alternatingGroup (Fin 8))
    (hS : IsSylowIn 2 S (alternatingGroup (Fin 8))) (hSK : S ≤ K)
    (hne : K ≠ alternatingGroup (Fin 8)) :
    ∃ Q : Subgroup (Perm (Fin 8)), Q ≤ K ∧ (Q.subgroupOf K).Normal ∧ IsPGroup 2 Q ∧
      K ⊓ Subgroup.centralizer (Q : Set (Perm (Fin 8))) ≤ Q := by
  obtain ⟨g, hgA, hgS⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_D hS
  set h : Perm (Fin 8) := g⁻¹ with hh
  have hhA : h ∈ alternatingGroup (Fin 8) := by
    rw [hh]
    exact (alternatingGroup (Fin 8)).inv_mem hgA
  have hhD : Even8.D = B6.conjSub h S := by
    have : B6.conjSub h S = Even8.D := by
      rw [hgS, hh, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
    exact this.symm
  set K' : Subgroup (Perm (Fin 8)) := B6.conjSub h K with hK'def
  have hK'A : K' ≤ alternatingGroup (Fin 8) := by
    have hfix : B6.conjSub h (alternatingGroup (Fin 8)) = alternatingGroup (Fin 8) :=
      B6.conjSub_eq_self (Subgroup.le_normalizer hhA)
    calc K' = B6.conjSub h K := hK'def
      _ ≤ B6.conjSub h (alternatingGroup (Fin 8)) := (B6.conjSub h).le_iff_le.mpr hK
      _ = alternatingGroup (Fin 8) := hfix
  have hDK' : Even8.D ≤ K' := by
    calc Even8.D = B6.conjSub h S := hhD
      _ ≤ B6.conjSub h K := (B6.conjSub h).le_iff_le.mpr hSK
      _ = K' := hK'def.symm
  set Y : Subgroup ↥(alternatingGroup (Fin 8)) :=
    K'.subgroupOf (alternatingGroup (Fin 8)) with hYdef
  have hDY : Even8.D.subgroupOf (alternatingGroup (Fin 8)) ≤ Y := by
    rw [hYdef]
    exact Subgroup.subgroupOf_mono (alternatingGroup (Fin 8)) hDK'
  rcases Even8.overgroups Y hDY with hYtop | hYchar
  · exfalso
    have hK'eq : K' = alternatingGroup (Fin 8) := by
      have hle : alternatingGroup (Fin 8) ≤ K' :=
        Subgroup.subgroupOf_eq_top.mp (hYdef ▸ hYtop)
      exact le_antisymm hK'A hle
    apply hne
    have hconj : B6.conjSub h⁻¹ K' = K := by
      rw [hK'def, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
    have htmp : K = alternatingGroup (Fin 8) := by
      have h' := congrArg (B6.conjSub h⁻¹) hK'eq
      rwa [hconj, B6.conjSub_eq_self
        (Subgroup.le_normalizer ((alternatingGroup (Fin 8)).inv_mem hhA))] at h'
    exact htmp
  · have hcharK' : CharTwo K' := charTwo_of_subgroupOf hK'A (hYdef ▸ hYchar)
    set Q' : Subgroup (Perm (Fin 8)) := pCoreOf 2 K' with hQ'def
    have hspecQ := pCoreOf_spec K' hcharK'
    rw [← hQ'def] at hspecQ
    obtain ⟨hQ'le, hQ'norm, hQ'2, hQ'cent⟩ := hspecQ
    refine ⟨B6.conjSub h⁻¹ Q', ?_⟩
    have hspec := conjSub_spec (g := h⁻¹) hQ'le hQ'norm hQ'2 hQ'cent
    have hK'conj : B6.conjSub h⁻¹ K' = K := by
      rw [hK'def, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
    rw [hK'conj] at hspec
    exact hspec

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
