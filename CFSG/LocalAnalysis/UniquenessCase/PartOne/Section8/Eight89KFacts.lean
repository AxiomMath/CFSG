module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

private lemma k89kf_conj_mod_iff {G : Type} [Group G] {L O : Subgroup G} {ω z y l : G}
    (hLO : L ≤ normalizer (O : Set G)) (hω : ω = z * y) (hl : l ∈ L) (hz : z ∈ L)
    (hy : y * l * y⁻¹ * l⁻¹ ∈ O) :
    l⁻¹ * (ω * l * ω⁻¹) ∈ O ↔ l⁻¹ * (z * l * z⁻¹) ∈ O := by
  have hdiff : (l⁻¹ * (ω * l * ω⁻¹)) * (l⁻¹ * (z * l * z⁻¹))⁻¹ ∈ O := by
    have hkey : ω * l * ω⁻¹ = (z * (y * l * y⁻¹ * l⁻¹) * z⁻¹) * (z * l * z⁻¹) := by
      rw [hω]
      have hyconj : y * l * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * l := by group
      rw [hyconj]
      group
    have hzO : z * (y * l * y⁻¹ * l⁻¹) * z⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (hLO hz) _).1 hy
    have hlO : l⁻¹ * (z * (y * l * y⁻¹ * l⁻¹) * z⁻¹) * l ∈ O :=
      (Subgroup.mem_normalizer_iff''.1 (hLO hl) _).1 hzO
    rw [hkey]
    convert hlO using 1
    group
  constructor
  · intro hA
    have hBinv : (l⁻¹ * (z * l * z⁻¹))⁻¹ ∈ O := by
      have h1 : (l⁻¹ * (ω * l * ω⁻¹))⁻¹ * ((l⁻¹ * (ω * l * ω⁻¹)) *
          (l⁻¹ * (z * l * z⁻¹))⁻¹) ∈ O := O.mul_mem (O.inv_mem hA) hdiff
      rwa [inv_mul_cancel_left] at h1
    simpa using O.inv_mem hBinv
  · intro hB
    have hA : l⁻¹ * (ω * l * ω⁻¹) ∈ O := by
      have h1 : (l⁻¹ * (ω * l * ω⁻¹)) * (l⁻¹ * (z * l * z⁻¹))⁻¹ *
          (l⁻¹ * (z * l * z⁻¹)) ∈ O := O.mul_mem hdiff hB
      simpa [mul_assoc] using h1
    exact hA

private lemma k89kf_centralizer_singleton_le_zpowers {G : Type} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (show Commute x g from hg x (by simp)) k).eq

private lemma k89kf_mem_pCore_iff {G : Type} [Group G] {L O : Subgroup G}
    (hO : O = pCoreOf 2 L) (w : ↥L) : w ∈ CFSG.pCore 2 ↥L ↔ (w : G) ∈ O := by
  rw [hO]
  constructor
  · intro hw; exact Subgroup.mem_map_of_mem L.subtype hw
  · intro hw
    rcases Subgroup.mem_map.mp hw with ⟨n, hn, hnx⟩
    have : n = w := Subtype.ext hnx
    rwa [this] at hn

private lemma k89kf_le_of_isPGroup_quotient {G : Type} [Group G] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) {C K H : Subgroup G}
    [hKn : (K.subgroupOf C).Normal] (hHC : H ≤ C) (_hKC : K ≤ C) (hH : IsPGroup q H)
    (hquot : IsPGroup p (↥C ⧸ K.subgroupOf C)) : H ≤ K := by
  let ρ : ↥C →* ↥C ⧸ K.subgroupOf C := QuotientGroup.mk' (K.subgroupOf C)
  have hHsub : IsPGroup q (H.subgroupOf C) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHC).symm
  have hmap : IsPGroup q ((H.subgroupOf C).map ρ) := hHsub.map ρ
  have hmap2 : IsPGroup p ((H.subgroupOf C).map ρ) :=
    hquot.of_injective ((H.subgroupOf C).map ρ).subtype Subtype.coe_injective
  have hdisj := IsPGroup.disjoint_of_ne q p (Ne.symm hpq) _ _ hmap hmap2
  have hbot : (H.subgroupOf C).map ρ = ⊥ := by
    have := disjoint_iff.mp hdisj
    rwa [inf_idem] at this
  intro x hx
  have hxC : x ∈ C := hHC hx
  have hxker : (⟨x, hxC⟩ : ↥C) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    have hmem : ρ ⟨x, hxC⟩ ∈ (H.subgroupOf C).map ρ :=
      Subgroup.mem_map_of_mem ρ (show (⟨x, hxC⟩ : ↥C) ∈ H.subgroupOf C from hx)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  rwa [show ρ.ker = K.subgroupOf C from QuotientGroup.ker_mk' _] at hxker

private lemma k89kf_normal_dichotomy {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (M.map (QuotientGroup.mk' (Subgroup.center Q))) with h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator Q ≤ M := by
      have e : commutator Q = ⁅M ⊔ Subgroup.center Q, M ⊔ Subgroup.center Q⁆ := by
        rw [hMZ]; rfl
      rw [e]
      have hn : (M ⊔ Subgroup.center Q).Normal := by rw [hMZ]; infer_instance
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    have hperf' : commutator Q = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [hperf'] at hle
    exact top_le_iff.mp hle

private lemma k89kf_Hinf_eq_self_of_isPerfect {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hperf : Group.IsPerfect ↥H) : Hinf H = H := by
  have hPR : CFSG.perfectResidual ↥H = ⊤ := by
    have htop : Group.IsPerfect ↥(⊤ : Subgroup ↥H) := (Group.IsPerfect.top_iff (G := ↥H)).mpr hperf
    have h := (CFSG.perfect_residual_transport (G := ↥H) (H := ↥H)
      (MonoidHom.id ↥H)).2.2 (⊤ : Subgroup ↥H) htop
    exact top_le_iff.mp h
  change (CFSG.perfectResidual ↥H).map H.subtype = H
  rw [hPR, Subgroup.map_top, Subgroup.range_subtype]

private lemma k89kf_isA6Z3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsA6Z3 Y) : IsA6Z3 X := by
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv e h.1, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective (K := Subgroup.center X) (f := e.toMonoidHom)
      e.injective,
      show Subgroup.map e.toMonoidHom (Subgroup.center X) = Subgroup.center Y from
        Subgroup.map_center_eq e, h.2.1]
  · obtain ⟨f⟩ := h.2.2
    exact ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
      (Subgroup.map_center_eq e)).trans f⟩

private lemma k89kf_pCore_eq_bot_of_isA6Z3 {X : Type} [Group X] [Finite X] (h : IsA6Z3 X) :
    CFSG.pCore 2 X = ⊥ := by
  have hnorm : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal (p := 2) (G := X)
  have h2X : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  rcases @k89kf_normal_dichotomy X _ h.1 (CFSG.pCore 2 X) hnorm with hle | htop
  · have h3X : IsPGroup 3 ↥(Subgroup.center X) :=
      IsPGroup.of_card (n := 1) (by rw [h.2.1]; norm_num)
    have hdisj : Disjoint (CFSG.pCore 2 X) (Subgroup.center X) :=
      IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2X h3X
    have := disjoint_iff.mp hdisj
    rwa [inf_eq_left.mpr hle] at this
  · exfalso
    have htop2 : IsPGroup 2 ↥(⊤ : Subgroup X) := htop ▸ h2X
    have h2Y : IsPGroup 2 X := htop2.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := h2Y.exists_card_eq
    have h3dvd : 3 ∣ Nat.card X := by
      rw [← h.2.1]
      simpa using Subgroup.card_dvd_of_le (show Subgroup.center X ≤ ⊤ from le_top)
    rw [hk] at h3dvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3dvd) (by norm_num)

theorem s889_facts {G : Type} [Group G] [Finite G] (D : Data G)
    (h882 : R882 D) (h885 : R885 D) (h886 : R886 D) : AllFacts889 D := by
  intro L P ω hω
  classical
  set O : Subgroup G := pCoreOf 2 L with hO
  set Q : Subgroup G := P ⊓ L with hQ
  set Z : Subgroup G := ZOf Q with hZ
  set C : Subgroup G := L ⊓ centralizer ({ω} : Set G) with hC
  set K : Subgroup G := DerInf8 C with hK
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set Ĉ : Subgroup (Bar2 L) :=
    Subgroup.centralizer (((Z.subgroupOf L).map π : Subgroup (Bar2 L)) : Set (Bar2 L)) with hĈ
  obtain ⟨hZcard, hXexists, hWeak, hĈA6⟩ := h886 L P hω.set880
  have hLO : L ≤ normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hO_le_L : O ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hPL : P ≤ D.M := hω.set880.sylow.le
  have hML : D.M ≤ normalizer (L : Set G) := r889_normalizes_of_inputs h882 h885 hω.set880
  have hMO : D.M ≤ normalizer (O : Set G) :=
    hML.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hZ_le_Q : Z ≤ Q := by rw [hZ]; exact inf_le_left
  have hZ_le_L : Z ≤ L := hZ_le_Q.trans inf_le_right
  obtain ⟨z, hzZ, y, hyC, hzy⟩ := hω.fac
  have hy : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ O := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hyC).2
  have hzQ : z ∈ Q := hZ_le_Q hzZ
  have hzL : z ∈ L := hZ_le_L hzZ
  have hz_ne : z ≠ 1 := by
    intro hz1
    apply hω.notC
    rw [hzy, hz1, one_mul]
    exact hyC
  have hzorder : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard Z hzZ
      rwa [hZcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz_ne
    · exact h
  have hZ_zpowers : Z = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers z) (K := Z)
      (Subgroup.zpowers_le.mpr hzZ) ?_).symm
    rw [Nat.card_zpowers, hZcard, hzorder]
  have hCL : C ≤ L := by rw [hC]; exact inf_le_left
  have hKC : K ≤ C := by
    rw [hK]
    exact Subgroup.map_subtype_le _
  have hKL : K ≤ L := hKC.trans hCL
  have hsub_zpowers :
      (Subgroup.zpowers z).subgroupOf L = Subgroup.zpowers (⟨z, hzL⟩ : ↥L) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by apply Subtype.ext; simpa using hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hmapZ : (Z.subgroupOf L).map π = Subgroup.zpowers (π ⟨z, hzL⟩) := by
    rw [hZ_zpowers, hsub_zpowers, MonoidHom.map_zpowers]
  have hπC : (C.subgroupOf L).map π = Ĉ := by
    apply le_antisymm
    · rintro x ⟨c, hc, rfl⟩
      have hcC : (c : G) ∈ C := hc
      have hcL : (c : G) ∈ L := hCL hcC
      have hcω : ω * (c : G) = (c : G) * ω := by
        have h : (c : G) ∈ Subgroup.centralizer ({ω} : Set G) := (hC ▸ hcC).2
        exact (Subgroup.mem_centralizer_iff.mp h) ω (by simp)
      have hcz : (c : G) * z * (c : G)⁻¹ * z⁻¹ ∈ O := by
        have h1 : (c : G)⁻¹ * (z * (c : G) * z⁻¹) ∈ O :=
          (k89kf_conj_mod_iff hLO hzy hcL hzL (hy (c : G) hcL)).1 (by
            have h2 : (c : G)⁻¹ * (ω * (c : G) * ω⁻¹) = 1 := by rw [hcω]; group
            rw [h2]; exact O.one_mem)
        have h2 : (c : G) * ((c : G)⁻¹ * (z * (c : G) * z⁻¹)) * (c : G)⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.1 (hLO hcL) _).1 h1
        have h3 : z * (c : G) * z⁻¹ * (c : G)⁻¹ ∈ O := by convert h2 using 1; group
        have h4 := O.inv_mem h3
        convert h4 using 1; group
      have hcomm : π c ∈ Subgroup.centralizer ({π ⟨z, hzL⟩} : Set (Bar2 L)) := by
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hdiv : ((⟨z, hzL⟩ : ↥L) * c) / (c * ⟨z, hzL⟩) ∈ CFSG.pCore 2 ↥L := by
          rw [k89kf_mem_pCore_iff hO]
          convert O.inv_mem hcz using 1
          simp only [Subgroup.coe_div, Subgroup.coe_mul]
          rw [div_eq_mul_inv]
          group
        rw [← map_mul, ← map_mul]
        exact QuotientGroup.eq_iff_div_mem.mpr hdiv
      rw [hĈ, hmapZ]
      exact k89kf_centralizer_singleton_le_zpowers _ hcomm
    · intro x hx
      rw [hĈ] at hx
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
      have hbL : (b : G) ∈ L := b.2
      have hbz : (b : G) * z * (b : G)⁻¹ * z⁻¹ ∈ O := by
        have hzmap : π ⟨z, hzL⟩ ∈ (Z.subgroupOf L).map π :=
          Subgroup.mem_map_of_mem π (show (⟨z, hzL⟩ : ↥L) ∈ Z.subgroupOf L from hzZ)
        have hcomm := (Subgroup.mem_centralizer_iff.1 hx) _ hzmap
        have hcomm' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (((⟨z, hzL⟩ : ↥L) * b)) =
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (b * ⟨z, hzL⟩) := by
          have h1 := hcomm
          rw [← map_mul, ← map_mul] at h1
          exact h1
        have h1 : (((⟨z, hzL⟩ : ↥L) * b) / (b * ⟨z, hzL⟩) : ↥L) ∈ CFSG.pCore 2 ↥L :=
          QuotientGroup.eq_iff_div_mem.mp hcomm'
        have h1' := (k89kf_mem_pCore_iff hO _).mp h1
        have h1'' : z * (b : G) * z⁻¹ * (b : G)⁻¹ ∈ O := by
          convert h1' using 1
          simp only [Subgroup.coe_div, Subgroup.coe_mul]
          rw [div_eq_mul_inv]
          group
        have := O.inv_mem h1''
        convert this using 1
        group
      have hbz' : (b : G)⁻¹ * (z * (b : G) * z⁻¹) ∈ O := by
        have h1 : (b : G)⁻¹ * ((b : G) * z * (b : G)⁻¹ * z⁻¹) * (b : G) ∈ O :=
          (Subgroup.mem_normalizer_iff''.1 (hLO hbL) _).1 hbz
        have h2 : z * (b : G)⁻¹ * z⁻¹ * (b : G) ∈ O := by
          convert h1 using 1; group
        have h3 := O.inv_mem h2
        convert h3 using 1; group
      have hbω : (b : G)⁻¹ * (ω * (b : G) * ω⁻¹) ∈ O :=
        (k89kf_conj_mod_iff hLO hzy hbL hzL (hy (b : G) hbL)).2 hbz'
      obtain ⟨k, hk⟩ := hO2.exists_card_eq
      have hcop : Nat.Coprime (orderOf ω) (Nat.card O) := by
        rw [hω.order, hk]
        exact (show Nat.Coprime 3 2 by norm_num).pow_right k
      have hωN : ∀ n ∈ O, ω * n * ω⁻¹ ∈ O := fun n hn =>
        (Subgroup.mem_normalizer_iff.1 (hMO (hPL hω.mem.1)) n).1 hn
      obtain ⟨n, hnO, hfix⟩ := CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime O hωN hbω hcop
      have hbnL : (b : G) * n ∈ L := L.mul_mem hbL (hO_le_L hnO)
      have hbnC : (b : G) * n ∈ C := by
        rw [hC]
        refine ⟨hbnL, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst h
        have h2 : ω * ((b : G) * n) = ((b : G) * n) * ω := by
          calc ω * ((b : G) * n) = ω * ((b : G) * n) * ω⁻¹ * ω := by group
            _ = ((b : G) * n) * ω := by rw [hfix]
        exact h2
      refine Subgroup.mem_map.mpr ⟨⟨(b : G) * n, hbnL⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hbnC
      · have hnker : (⟨n, hO_le_L hnO⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
          (k89kf_mem_pCore_iff hO _).2 hnO
        have hn1 : π ⟨n, hO_le_L hnO⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hnker
        show π ⟨(b : G) * n, hbnL⟩ = π b
        rw [show (⟨(b : G) * n, hbnL⟩ : ↥L) = b * ⟨n, hO_le_L hnO⟩ from Subtype.ext rfl,
          map_mul, hn1, mul_one]
  have hπK : (K.subgroupOf L).map π = Ĉ := by
    have h1 : K.subgroupOf L = Hinf (C.subgroupOf L) := by
      rw [hK]
      change ((CFSG.perfectResidual ↥C).map C.subtype).subgroupOf L = Hinf (C.subgroupOf L)
      rw [CFSG.perfectResidual_subtype_subgroupOf C L hCL]
      rfl
    rw [h1, Hinf_map π (C.subgroupOf L), hπC]
    exact k89kf_Hinf_eq_self_of_isPerfect hĈA6.1.1
  have hKsub : K.subgroupOf C = CFSG.perfectResidual ↥C := by
    rw [hK]
    change ((CFSG.perfectResidual ↥C).map C.subtype).comap C.subtype = CFSG.perfectResidual ↥C
    rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  have hKn : (K.subgroupOf C).Normal := hKsub ▸ inferInstance
  have hCsup : C ≤ K ⊔ (C ⊓ O) := by
    intro c hc
    have hcL : c ∈ L := hCL hc
    have hmem : π ⟨c, hcL⟩ ∈ (K.subgroupOf L).map π := by
      rw [hπK, ← hπC]
      exact Subgroup.mem_map_of_mem π (show (⟨c, hcL⟩ : ↥L) ∈ C.subgroupOf L from hc)
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
    have hkK : (k : G) ∈ K := hk
    have hkcO : (k : G)⁻¹ * c ∈ O := by
      have hkc' : π (k⁻¹ * ⟨c, hcL⟩) = 1 := by
        rw [map_mul, map_inv, hkeq, inv_mul_cancel]
      exact (k89kf_mem_pCore_iff hO _).mp ((QuotientGroup.eq_one_iff _).mp hkc')
    have hkcC : (k : G)⁻¹ * c ∈ C := C.mul_mem (C.inv_mem (hKC hkK)) hc
    have hceq : c = (k : G) * ((k : G)⁻¹ * c) := by group
    rw [hceq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkK)
      (Subgroup.mem_sup_right ⟨hkcC, hkcO⟩)
  have hCeq : C = K ⊔ (C ⊓ O) := le_antisymm hCsup (sup_le hKC inf_le_left)
  have hquotC : IsPGroup 2 (↥C ⧸ K.subgroupOf C) := by
    let ψ : ↥(C ⊓ O) →* (↥C ⧸ K.subgroupOf C) :=
      (QuotientGroup.mk' (K.subgroupOf C)).comp
        (Subgroup.inclusion (show C ⊓ O ≤ C from inf_le_left))
    have hψsurj : Function.Surjective ψ := by
      intro z
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf C) z
      have hcL : (c : G) ∈ L := hCL c.2
      have hmem : π ⟨(c : G), hcL⟩ ∈ (K.subgroupOf L).map π := by
        rw [hπK, ← hπC]
        exact Subgroup.mem_map_of_mem π (show (⟨(c : G), hcL⟩ : ↥L) ∈ C.subgroupOf L from c.2)
      obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
      have hkK : (k : G) ∈ K := hk
      have hkcO : (k : G)⁻¹ * (c : G) ∈ O := by
        have hkc' : π (k⁻¹ * ⟨(c : G), hcL⟩) = 1 := by
          rw [map_mul, map_inv, hkeq, inv_mul_cancel]
        exact (k89kf_mem_pCore_iff hO _).mp ((QuotientGroup.eq_one_iff _).mp hkc')
      have ho_mem : (k : G)⁻¹ * (c : G) ∈ C ⊓ O :=
        ⟨C.mul_mem (C.inv_mem (hKC hkK)) c.2, hkcO⟩
      refine ⟨⟨(k : G)⁻¹ * (c : G), ho_mem⟩, ?_⟩
      show QuotientGroup.mk' (K.subgroupOf C) (⟨(k : G)⁻¹ * (c : G), ho_mem.1⟩ : ↥C) =
        QuotientGroup.mk' (K.subgroupOf C) c
      have hco : (⟨(k : G)⁻¹ * (c : G), ho_mem.1⟩ : ↥C) =
          (⟨(k : G), hKC hkK⟩ : ↥C)⁻¹ * c := by ext; rfl
      rw [hco, map_mul, map_inv]
      have hk1 : QuotientGroup.mk' (K.subgroupOf C) (⟨(k : G), hKC hkK⟩ : ↥C) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr
          (show (⟨(k : G), hKC hkK⟩ : ↥C) ∈ K.subgroupOf C from hkK)
      rw [hk1, inv_one, one_mul]
    exact IsPGroup.of_surjective (hO2.to_le (show C ⊓ O ≤ O from inf_le_right)) ψ hψsurj
  have hQK : Q ≤ K := by
    have hQC : Q ≤ C := by
      rw [hQ, hC]
      refine le_inf inf_le_right ?_
      intro q hq
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact ((Subgroup.mem_centralizer_iff.mp hω.mem.2) q (Subgroup.mem_inf.mp hq).1).symm
    have hQ3 : IsPGroup 3 Q := by
      rw [hQ]
      exact hω.set880.sylow.isPGroup.to_le inf_le_left
    exact k89kf_le_of_isPGroup_quotient (p := 2) (q := 3) (by norm_num) hQC hKC hQ3 hquotC
  have hZK : Z ≤ K := hZ_le_Q.trans hQK
  have hcoreĈ : CFSG.pCore 2 ↥Ĉ = ⊥ := k89kf_pCore_eq_bot_of_isA6Z3 hĈA6
  let πK : ↥K →* Bar2 L := π.comp (Subgroup.inclusion hKL)
  have hrange : πK.range = Ĉ := by
    rw [MonoidHom.range_comp]
    have hinc : (Subgroup.inclusion hKL).range = K.subgroupOf L := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩
    rw [hinc, hπK]
  have hker : IsPGroup 2 πK.ker := by
    have hker_eq : πK.ker = (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hKL) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      exact QuotientGroup.eq_one_iff _
    rw [hker_eq]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective
      (Subgroup.inclusion hKL) (Subgroup.inclusion_injective hKL)
  let φ : ↥K →* ↥Ĉ := πK.codRestrict Ĉ (fun x => hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : Bar2 L) ∈ πK.range := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    refine ⟨x, ?_⟩
    exact Subtype.ext hx
  have hφker : IsPGroup 2 φ.ker := by
    have hkerφ : φ.ker = πK.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [hkerφ]; exact hker
  have hpCoreK : CFSG.pCore 2 ↥K = φ.ker := by
    refine le_antisymm ?_ ?_
    · have hmap := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker φ hφsurj hφker
      rw [hcoreĈ] at hmap
      exact (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥K)).mp hmap
    · exact le_sSup ⟨inferInstance, hφker⟩
  have hKO_pCore : ∀ x : ↥K, (x : G) ∈ O → x ∈ CFSG.pCore 2 ↥K := by
    intro x hx
    have hKOs : (K ⊓ O).subgroupOf K = (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hKL) := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      constructor
      · rintro ⟨-, hyO⟩
        exact (k89kf_mem_pCore_iff hO _).mpr hyO
      · intro hy
        exact ⟨y.2, (k89kf_mem_pCore_iff hO _).mp hy⟩
    have hKOp : IsPGroup 2 ((K ⊓ O).subgroupOf K) := by
      rw [hKOs]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective
        (Subgroup.inclusion hKL) (Subgroup.inclusion_injective hKL)
    have hKOn : ((K ⊓ O).subgroupOf K).Normal := by
      rw [hKOs]; infer_instance
    have hle : (K ⊓ O).subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hKOn, hKOp⟩
    exact hle (by rw [Subgroup.mem_subgroupOf]; exact ⟨x.2, hx⟩)
  have hBar2K : Nonempty (Bar2 K ≃* ↥Ĉ) := by
    obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker φ hφsurj hφker
    exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hcoreĈ).trans QuotientGroup.quotientBot)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ⁅F07.DerInf C, F07.DerInf C⁆ = F07.DerInf C
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.derInf_isPerfect C
  · change IsA6Z3 (Bar2 K)
    obtain ⟨e⟩ := hBar2K
    exact k89kf_isA6Z3_of_mulEquiv e hĈA6
  · change IsA6Z3 ↥((K.subgroupOf L).map π)
    rw [hπK]
    exact hĈA6
  · change Q ≤ K
    exact hQK
  ·
    change ((Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) = Subgroup.center (Bar2 K)
    have hzK : z ∈ K := hZK hzZ
    have hmapZK : (Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
        Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨z, hZK hzZ⟩ : ↥K)) := by
      have hsubK : (Subgroup.zpowers z).subgroupOf K =
          Subgroup.zpowers (⟨z, hZK hzZ⟩ : ↥K) := by
        ext x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
        constructor
        · rintro ⟨m, hm⟩
          exact ⟨m, by apply Subtype.ext; simpa using hm⟩
        · rintro ⟨m, hm⟩
          exact ⟨m, by simpa using congrArg Subtype.val hm⟩
      rw [hZ_zpowers, hsubK, MonoidHom.map_zpowers]
    have hzbar_ne : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨z, hZK hzZ⟩ : ↥K) ≠ 1 := by
      intro h1
      have hmem : (⟨z, hZK hzZ⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
        (QuotientGroup.eq_one_iff _).mp h1
      have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
      have hdvd : orderOf (⟨z, hZK hzZ⟩ : ↥K) ∣ Nat.card ↥(CFSG.pCore 2 ↥K) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      obtain ⟨j, hj⟩ := h2.exists_card_eq
      rw [hj] at hdvd
      have hzord : orderOf (⟨z, hZK hzZ⟩ : ↥K) = 3 := by
        rw [← Subgroup.orderOf_coe (⟨z, hZK hzZ⟩ : ↥K)]; exact hzorder
      rw [hzord] at hdvd
      exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
    have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨z, hZK hzZ⟩ : ↥K)) = 3 := by
      have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨z, hZK hzZ⟩ : ↥K)) ∣ 3 := by
        have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨z, hZK hzZ⟩ : ↥K)) ∣
            orderOf (⟨z, hZK hzZ⟩ : ↥K) := orderOf_map_dvd _ _
        rwa [show orderOf (⟨z, hZK hzZ⟩ : ↥K) = 3 from by
          rw [Subgroup.orderOf_mk]; exact hzorder] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hzbar_ne
      · exact h
    have hcardZK : Nat.card ((Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) = 3 := by
      rw [hmapZK, Nat.card_zpowers, hord]
    have hle : (Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≤
        Subgroup.center (Bar2 K) := by
      rw [hmapZK]
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
      have hxL : (x : G) ∈ L := hKL x.2
      have hxĈ : π ⟨(x : G), hxL⟩ ∈ Ĉ := by
        rw [← hπK]
        exact Subgroup.mem_map_of_mem π (show (⟨(x : G), hxL⟩ : ↥L) ∈ K.subgroupOf L from x.2)
      have hzmap : π ⟨z, hzL⟩ ∈ (Z.subgroupOf L).map π :=
        Subgroup.mem_map_of_mem π (show (⟨z, hzL⟩ : ↥L) ∈ Z.subgroupOf L from hzZ)
      have hcomm := (Subgroup.mem_centralizer_iff.mp hxĈ) _ hzmap
      have hxzO : (x : G) * z * (x : G)⁻¹ * z⁻¹ ∈ O := by
        have hq : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
              ((⟨(x : G), hxL⟩ : ↥L) * ⟨z, hzL⟩) =
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (⟨z, hzL⟩ * ⟨(x : G), hxL⟩) := by
          have h1 := hcomm
          rw [← map_mul, ← map_mul] at h1
          exact h1.symm
        have hdiv : ((⟨(x : G), hxL⟩ : ↥L) * ⟨z, hzL⟩) / (⟨z, hzL⟩ * ⟨(x : G), hxL⟩) ∈
            CFSG.pCore 2 ↥L := QuotientGroup.eq_iff_div_mem.mp hq
        have hdivO : ((((⟨(x : G), hxL⟩ : ↥L) * ⟨z, hzL⟩) /
            (⟨z, hzL⟩ * ⟨(x : G), hxL⟩) : ↥L) : G) ∈ O :=
          (k89kf_mem_pCore_iff hO _).mp hdiv
        convert hdivO using 1
        simp only [Subgroup.coe_div, Subgroup.coe_mul]
        rw [div_eq_mul_inv]; group
      have hxzK : (x : G) * z * (x : G)⁻¹ * z⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem x.2 hzK) (K.inv_mem x.2)) (K.inv_mem hzK)
      have hmem : (⟨(x : G) * z * (x : G)⁻¹ * z⁻¹, hxzK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
        hKO_pCore _ hxzO
      let y' : Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) x
      let z' : Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨z, hZK hzZ⟩ : ↥K)
      have hcommK : y' * z' = z' * y' := by
        rw [← map_mul, ← map_mul]
        refine QuotientGroup.eq_iff_div_mem.mpr ?_
        convert hmem using 1
        ext
        simp only [Subgroup.coe_div, Subgroup.coe_mul]
        rw [div_eq_mul_inv]; group
      exact hcommK
    have hcenterBar : Nat.card (Subgroup.center (Bar2 K)) = 3 := by
      obtain ⟨e⟩ := hBar2K
      rw [← Subgroup.card_map_of_injective (K := Subgroup.center (Bar2 K))
        (f := e.toMonoidHom) e.injective,
        show Subgroup.map e.toMonoidHom (Subgroup.center (Bar2 K)) = Subgroup.center ↥Ĉ from
          Subgroup.map_center_eq e, hĈA6.2.1]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZK, hcenterBar])

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
