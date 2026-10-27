module

public import CFSG.Quasithin.Vol2.Asc94.TS40e
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def Frame3.D (F : Frame3 G z) : Subgroup G := F.A ⊓ F.U

@[expose] def Frame3.Dc (F : Frame3 G z) (l : G) : Subgroup G := cjS l⁻¹ F.D

theorem Frame3.mem_Dc (F : Frame3 G z) {l x : G} : x ∈ F.Dc l ↔ l * x * l⁻¹ ∈ F.D := by
  show x ∈ cjS l⁻¹ F.D ↔ _
  rw [Gen.mem_cj, inv_inv]

theorem Frame3.Dc_one (F : Frame3 G z) : F.Dc 1 = F.D := by
  ext x
  rw [F.mem_Dc]
  simp

theorem Frame3.z_mem_D (F : Frame3 G z) : z ∈ F.D := ⟨F.z_mem_A, F.toFrame1.toFrame0.z_mem_U⟩

theorem Frame3.NA_le_normalizer_D (F : Frame3 G z) {n : G} (hn : n ∈ F.NA) :
    n ∈ Subgroup.normalizer (F.D : Set G) := by
  have h := s39_6_4 F.toFrame2
  have : n ∈ Subgroup.normalizer ((F.A ⊓ F.U : Subgroup G) : Set G) := by
    rw [h]
    exact ⟨hn.2, F.toFrame1.toFrame0.le_normalizer_U hn.1⟩
  exact this

theorem Frame3.normalizer_D_inf (F : Frame3 G z) (hII : Subgroup.normalizer (F.U : Set G) = Cz z)
    {n : G} (hnL : n ∈ Subgroup.normalizer (F.A : Set G))
    (hnD : n ∈ Subgroup.normalizer (F.D : Set G)) : n ∈ F.NA := by
  have h := s39_6_4 F.toFrame2
  have h2 : n ∈ Subgroup.normalizer ((F.A ⊓ F.U : Subgroup G) : Set G) := hnD
  rw [h] at h2
  have h3 : n ∈ Subgroup.normalizer (F.U : Set G) := h2.2
  rw [hII] at h3
  exact ⟨h3, hnL⟩

theorem Frame3.card_Dc (F : Frame3 G z) (l : G) : Nat.card (F.Dc l) = 8 := by
  show Nat.card (cjS l⁻¹ F.D) = 8
  rw [Gen.card_conjSubgroup]
  exact F.card_A_U

theorem Frame3.Dc_sub_Sz (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u) {l x : G}
    (hl : l ∈ Subgroup.normalizer (F.A : Set G)) (hx : x ∈ F.Dc l) (hx1 : x ≠ 1) : x ∈ F.Sz := by
  rw [F.mem_Dc] at hx
  have hd1 : l * x * l⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = l⁻¹ * (l * x * l⁻¹) * l := by group
    rw [this, h]
    group
  have hdS : l * x * l⁻¹ ∈ F.Sz := ⟨hx.1, hd1, hU1 _ hx.2 hd1⟩
  have := F.conj_mem_Sz hdS hl
  rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at this

theorem Frame3.Dc_eq (F : Frame3 G z) {l l' : G} (hl : l ∈ Subgroup.normalizer (F.A : Set G))
    (hl' : l' ∈ Subgroup.normalizer (F.A : Set G)) (h : l⁻¹ * z * l = l'⁻¹ * z * l') :
    F.Dc l = F.Dc l' := by
  have hnL : l' * l⁻¹ ∈ Subgroup.normalizer (F.A : Set G) :=
    Subgroup.mul_mem _ hl' (Subgroup.inv_mem _ hl)
  have hnz : l' * l⁻¹ ∈ Cz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (l' * l⁻¹) * z = l' * (l⁻¹ * z * l) * l'⁻¹ * (l' * l⁻¹) := by group
      _ = l' * (l'⁻¹ * z * l') * l'⁻¹ * (l' * l⁻¹) := by rw [h]
      _ = z * (l' * l⁻¹) := by group
  have hn := F.NA_le_normalizer_D (show l' * l⁻¹ ∈ F.NA from ⟨hnz, hnL⟩)
  ext x
  rw [F.mem_Dc, F.mem_Dc, show l' * x * l'⁻¹ = (l' * l⁻¹) * (l * x * l⁻¹) * (l' * l⁻¹)⁻¹ by group]
  exact Subgroup.mem_normalizer_iff.1 hn _

theorem Frame3.Dc_inj (F : Frame3 G z) (hII : Subgroup.normalizer (F.U : Set G) = Cz z) {l l' : G}
    (hl : l ∈ Subgroup.normalizer (F.A : Set G)) (hl' : l' ∈ Subgroup.normalizer (F.A : Set G))
    (h : F.Dc l = F.Dc l') : l⁻¹ * z * l = l'⁻¹ * z * l' := by
  have hnL : l' * l⁻¹ ∈ Subgroup.normalizer (F.A : Set G) :=
    Subgroup.mul_mem _ hl' (Subgroup.inv_mem _ hl)
  have hn : l' * l⁻¹ ∈ Subgroup.normalizer (F.D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have e1 : (l⁻¹ * d * l) ∈ F.Dc l ↔ d ∈ F.D := by
      rw [F.mem_Dc, show l * (l⁻¹ * d * l) * l⁻¹ = d by group]
    have e2 : (l⁻¹ * d * l) ∈ F.Dc l' ↔ (l' * l⁻¹) * d * (l' * l⁻¹)⁻¹ ∈ F.D := by
      rw [F.mem_Dc, show l' * (l⁻¹ * d * l) * l'⁻¹ = (l' * l⁻¹) * d * (l' * l⁻¹)⁻¹ by group]
    rw [← e1, ← e2, h]
  have hnN : l' * l⁻¹ ∈ F.NA := F.normalizer_D_inf hII hnL hn
  have hc := Subgroup.mem_centralizer_singleton_iff.1 hnN.1
  calc l⁻¹ * z * l = l⁻¹ * ((l' * l⁻¹)⁻¹ * ((l' * l⁻¹) * z)) * l := by group
    _ = l⁻¹ * ((l' * l⁻¹)⁻¹ * (z * (l' * l⁻¹))) * l := by rw [hc]
    _ = l'⁻¹ * z * l' := by group

theorem Frame3.card_stab_le (F : Frame3 G z) {g : G} (hg : g ∈ Subgroup.normalizer (F.A : Set G)) :
    Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) ≤
      Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨g * (x : G) * g⁻¹, ?_⟩) ?_
  · obtain ⟨hxN, hxa⟩ := x.2
    have hxz := Subgroup.mem_centralizer_singleton_iff.1 hxN.1
    have hxa' := Subgroup.mem_centralizer_singleton_iff.1 hxa
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc g * (x : G) * g⁻¹ * z = g * ((x : G) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * (x : G)) * g⁻¹ := by rw [hxa']
        _ = z * (g * (x : G) * g⁻¹) := by group
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxN.2) (Subgroup.inv_mem _ hg)
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc g * (x : G) * g⁻¹ * (g * z * g⁻¹) = g * ((x : G) * z) * g⁻¹ := by group
        _ = g * (z * (x : G)) * g⁻¹ := by rw [hxz]
        _ = g * z * g⁻¹ * (g * (x : G) * g⁻¹) := by group
  · intro x y hxy
    have := congrArg Subtype.val hxy
    have h2 : g * (x : G) * g⁻¹ = g * (y : G) * g⁻¹ := this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))

theorem Frame3.card_stab_eq (F : Frame3 G z) {g : G} (hg : g ∈ Subgroup.normalizer (F.A : Set G)) :
    Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) =
      Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) := by
  apply le_antisymm (F.card_stab_le hg)
  have := F.card_stab_le (Subgroup.inv_mem _ hg)
  simpa using this

theorem Frame3.orbit_eq (F : Frame3 G z) {i : Fin 7} {a : G} (ha : a ∈ F.Δ i) :
    {x : G | ∃ l ∈ F.NA, x = l⁻¹ * a * l} = F.Δ i := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact F.Δ_inv i a ha l hl
  · intro hx
    obtain ⟨l, hl, hxl⟩ := F.Δ_trans i a ha x hx
    exact ⟨l, hl, hxl⟩

theorem Frame3.orbit_ncard (F : Frame3 G z) {i : Fin 7} {a : G} (ha : a ∈ F.Δ i) :
    (F.Δ i).ncard * Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({a} : Set G)) = Nat.card ↥F.NA :=
  card_orbit_eq_ncard F.NA a (F.Δ i) (F.orbit_eq ha)

theorem Frame3.symm_D (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u) {l : G}
    (hl : l ∈ Subgroup.normalizer (F.A : Set G)) (h : l * z * l⁻¹ ∈ F.D) :
    l⁻¹ * z * l ∈ F.D := by
  have hz1 : z ≠ 1 := F.z_ne_one
  have hu1 : l * z * l⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : z = l⁻¹ * (l * z * l⁻¹) * l := by group
    rw [this, h1]
    group
  by_cases hu : l * z * l⁻¹ = z
  · have hc : l * z = z * l := by
      calc l * z = (l * z * l⁻¹) * l := by group
        _ = z * l := by rw [hu]
    have : l⁻¹ * z * l = z := by
      calc l⁻¹ * z * l = l⁻¹ * (z * l) := by group
        _ = l⁻¹ * (l * z) := by rw [hc]
        _ = z := by group
    rw [this]
    exact F.z_mem_D
  · have hu1mem : l * z * l⁻¹ ∈ F.Δ 1 := by
      rw [F.Δ1]
      exact ⟨h, by simp [hu1, hu]⟩
    have hzS : z ∈ F.Sz := ⟨F.z_mem_A, hz1, 1, by simp⟩
    have haSz : l⁻¹ * z * l ∈ F.Sz := F.conj_mem_Sz hzS hl
    have hg : l⁻¹ ∈ Subgroup.normalizer (F.A : Set G) := Subgroup.inv_mem _ hl
    have hstab := F.card_stab_eq hg
    simp only [inv_inv] at hstab
    have haU : l⁻¹ * z * l ∈ ⋃ i, F.Δ i := by
      rw [F.Δ_union]
      exact ⟨haSz.1, haSz.2.1⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 haU
    have hc : 0 < Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({l⁻¹ * z * l} : Set G)) :=
      Nat.card_pos
    have e1 := F.orbit_ncard hu1mem
    have e2 := F.orbit_ncard hi
    rw [hstab] at e1
    have hsz : (F.Δ i).ncard = (F.Δ 1).ncard := Nat.eq_of_mul_eq_mul_right hc (e2.trans e1.symm)
    have hiS : F.Δ i ⊆ F.Sz := by
      rcases F.dich i with h' | h'
      · exact h'
      · exact absurd haSz (Set.disjoint_left.1 h' hi)
    have hi1 : i = 1 := by
      have h6 : (F.Δ i).ncard = 6 := by
        rw [hsz, F.Δ_card 1]
        rfl
      have hi3 : i ≠ 3 := fun h3 => F.not_Δ3_sub_Sz (h3 ▸ hiS)
      rw [F.Δ_card i] at h6
      revert h6 hi3
      fin_cases i <;> simp
    subst hi1
    rw [F.Δ1] at hi
    exact hi.1

theorem Frame3.exists_l (F : Frame3 G z) {s : G} (hs : s ∈ F.Sz) :
    ∃ l ∈ Subgroup.normalizer (F.A : Set G), s = l⁻¹ * z * l := by
  obtain ⟨hsA, hs1, g, hg⟩ := hs
  obtain ⟨n, hn, hna⟩ := s39_6_3 F.toFrame2 F.z_mem_A hsA hg.symm
  exact ⟨n, hn, hna.symm⟩

open Classical in
@[expose] noncomputable def Frame3.Dm (F : Frame3 G z) (s : G) : Subgroup G :=
  if h : ∃ l ∈ Subgroup.normalizer (F.A : Set G), s = l⁻¹ * z * l then F.Dc (Classical.choose h)
  else ⊥

theorem Frame3.Dm_eq (F : Frame3 G z) {l : G} (hl : l ∈ Subgroup.normalizer (F.A : Set G)) :
    F.Dm (l⁻¹ * z * l) = F.Dc l := by
  classical
  have h : ∃ l' ∈ Subgroup.normalizer (F.A : Set G), l⁻¹ * z * l = l'⁻¹ * z * l' := ⟨l, hl, rfl⟩
  unfold Frame3.Dm
  rw [dif_pos h]
  obtain ⟨hl', hs⟩ := Classical.choose_spec h
  exact (F.Dc_eq hl hl' hs).symm

theorem Frame3.Dm_z (F : Frame3 G z) : F.Dm z = F.D := by
  have := F.Dm_eq (Subgroup.one_mem _ : (1 : G) ∈ Subgroup.normalizer (F.A : Set G))
  simpa [F.Dc_one] using this

theorem Frame3.mem_Dm_self (F : Frame3 G z) {s : G} (hs : s ∈ F.Sz) : s ∈ F.Dm s := by
  obtain ⟨l, hl, rfl⟩ := F.exists_l hs
  rw [F.Dm_eq hl, F.mem_Dc]
  rw [show l * (l⁻¹ * z * l) * l⁻¹ = z by group]
  exact F.z_mem_D

theorem Frame3.card_Dm (F : Frame3 G z) {s : G} (hs : s ∈ F.Sz) : Nat.card (F.Dm s) = 8 := by
  obtain ⟨l, hl, rfl⟩ := F.exists_l hs
  rw [F.Dm_eq hl]
  exact F.card_Dc l

theorem Frame3.Dm_sub_Sz (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u) {s t : G}
    (hs : s ∈ F.Sz) (ht : t ∈ F.Dm s) (ht1 : t ≠ 1) : t ∈ F.Sz := by
  obtain ⟨l, hl, rfl⟩ := F.exists_l hs
  rw [F.Dm_eq hl] at ht
  exact F.Dc_sub_Sz hU1 hl ht ht1

theorem Frame3.Dm_inj (F : Frame3 G z) (hII : Subgroup.normalizer (F.U : Set G) = Cz z) {s : G}
    (hs : s ∈ F.Sz) (h : F.Dm s = F.D) : s = z := by
  obtain ⟨l, hl, rfl⟩ := F.exists_l hs
  rw [F.Dm_eq hl, ← F.Dc_one] at h
  have := F.Dc_inj hII hl (Subgroup.one_mem _) h
  simpa using this

theorem Frame3.Dm_symm (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u) {s t : G}
    (hs : s ∈ F.Sz) (ht : t ∈ F.Sz) (h : t ∈ F.Dm s) : s ∈ F.Dm t := by
  obtain ⟨l, hl, rfl⟩ := F.exists_l hs
  obtain ⟨l', hl', rfl⟩ := F.exists_l ht
  rw [F.Dm_eq hl, F.mem_Dc] at h
  rw [F.Dm_eq hl', F.mem_Dc]
  have hg : (l' * l⁻¹)⁻¹ ∈ Subgroup.normalizer (F.A : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ hl' (Subgroup.inv_mem _ hl))
  have h1 : (l' * l⁻¹)⁻¹ * z * (l' * l⁻¹)⁻¹⁻¹ ∈ F.D := by
    rw [show (l' * l⁻¹)⁻¹ * z * (l' * l⁻¹)⁻¹⁻¹ = l * (l'⁻¹ * z * l') * l⁻¹ by group]
    exact h
  have h2 := F.symm_D hU1 hg h1
  rwa [show (l' * l⁻¹)⁻¹⁻¹ * z * (l' * l⁻¹)⁻¹ = l' * (l⁻¹ * z * l) * l'⁻¹ by group] at h2

theorem Frame3.mem_Dm_conj (F : Frame3 G z) {s t n : G} (hs : s ∈ F.Sz) (hn : n ∈ F.NA) :
    t ∈ F.Dm (n⁻¹ * s * n) ↔ n * t * n⁻¹ ∈ F.Dm s := by
  obtain ⟨l, hl, rfl⟩ := F.exists_l hs
  have hnL : n ∈ Subgroup.normalizer (F.A : Set G) := hn.2
  have hln : l * n ∈ Subgroup.normalizer (F.A : Set G) := Subgroup.mul_mem _ hl hnL
  have hz : n⁻¹ * (l⁻¹ * z * l) * n = (l * n)⁻¹ * z * (l * n) := by group
  rw [hz, F.Dm_eq hln, F.Dm_eq hl, F.mem_Dc, F.mem_Dc]
  rw [show l * n * t * (l * n)⁻¹ = l * (n * t * n⁻¹) * l⁻¹ by group]

end CFSG.Quasithin.A94
