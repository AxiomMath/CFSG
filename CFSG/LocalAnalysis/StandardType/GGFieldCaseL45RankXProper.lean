module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGD4FieldEnlargeE : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ φ : MulAut R, φ ^ 3 = 1 → φ ∉ (MulAut.conj : R →* MulAut R).range →
      (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) →
      ∀ E : Subgroup (MulAut R), IsElemAbelian 3 E → E ≤ (MulAut.conj : R →* MulAut R).range →
        Nat.card E ≤ 9 → (∀ e ∈ E, e * φ = φ * e) →
        ∃ r : R, MulAut.conj r ^ 3 = 1 ∧ (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) ∧
          MulAut.conj r * φ = φ * MulAut.conj r ∧ MulAut.conj r ∉ E

@[expose] def GGD4FieldEnlargeEInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .D → lab.rank = 4 →
    LargeEvenLabelAll lab GGD4FieldEnlargeE

@[expose] def GGD4CentreThreeInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H],
    LargeEvenMarking H (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4) →
      Nat.Coprime 3 (Nat.card (Subgroup.center H))

theorem ggL45D4BstarProperInput_of_enlarge (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hgr : GGNbrGraphInput) (hKG : GGD4FieldEnlargeEInput)
    (hZ : GGD4CentreThreeInput) : GGL45D4BstarProperInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hp3 hmk hm4 hBB
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hZK : Nat.Coprime 3 (Nat.card (Subgroup.center K)) := hZ K hmk
  have hUK := hcfg.le_normalizer
  have hBsU := hcfg.bs_le
  have hKp : commutator K = ⊤ := hcfg.2.2.2.2.2.2.2.1.2.2.1
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hxU : x ∈ U := hBsU hcfg.x_mem
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hUK hxU
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := fun b hb => hUK (hBsU hb)
  have hM1 := hgr G 3 B Bs x L D J hcfg.1.1 y K hcfg.2.2.2.2.2.1.2.2.1 hN _ hmk
  have hM2 := largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .D ∧ lab.rank = 4)
    (P' := fun R _ I F => GGD4FieldEnlargeE R I F ∧ GGRawThreeFixCyclic R I F)
    (fun lab hl hS Q hQ => by
      have h1 := hKG lab hl hS.1 hS.2 Q hQ
      have h2 := largeEvenLabelAll_d4ThreeFixCyclic hS.1 hS.2 _ h1
      exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨⟨hq, ha⟩, hb⟩ => ⟨hq, ha, hb⟩) h2)
    (fun _ _ _ _ _ _ h => h.1) hM1
  have hM3 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField 3)
    (fun lab hl _ => hraw 3 hp (by norm_num) lab hl) (fun _ _ _ _ _ _ _ => trivial) hM2
  have hM4 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := GGRawInndiagIso) (fun lab hl _ => hiso lab hl) (fun _ _ _ _ _ _ _ => trivial) hM3
  obtain ⟨-, lab₁, -, hraw₁⟩ := hM4
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨⟨⟨-, hgrθ⟩, hEnl, hTF⟩, hRIF⟩, hisoR⟩ :=
    largeEvenRawDatum_exists hraw₁
  obtain ⟨hI, -⟩ := hTF hs hna
  have hpart := hcfg.2.2.2.2.2.2.2.1
  have hM5 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField 3)
    (fun lab hl _ => hraw 3 hp (by norm_num) lab hl) (fun _ _ _ _ _ _ _ => trivial) hpart.2.2
  obtain ⟨-, lab', hlab', hraw2⟩ := hM5
  obtain ⟨R', _, I', F', ⟨hs', hna', θ', hU₁iff, hR'⟩, hisoRR'⟩ :=
    largeEvenRawDatum_exists (hisoR lab' hlab' _ hraw2)
  obtain ⟨hmul, hinv, hinn, -⟩ := hRIF hs hna
  obtain ⟨hmul', hinv', hinn', -⟩ := hR' hs' hna'
  have hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I) := fun u hu huN => by
    rw [hU₁iff u hu, ggL45_exists_induces_iff hinv' huN,
      ← ggL45_mem_ggInndiag_iff hmul' hinv' hinn', ← ggL45_mem_ggInndiag_iff hmul hinv hinn,
      hisoRR' hs' hna' (θ.symm.trans θ'), ← ggLAut_congr]
  subst hI
  have hinj := L45RankX.conj_injective_of_simple hs hna
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hB₁N : B₁ ≤ Subgroup.normalizer (K : Set G) := fun b hb => hUK (hBsU hb.1)
  set β : B₁ →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hB₁N) with hβ
  set E : Subgroup (MulAut R) := β.range with hEdef
  have hEmem : ∀ b ∈ B₁, ∀ hb : b ∈ Subgroup.normalizer (K : Set G), ggLAut K θ ⟨b, hb⟩ ∈ E :=
    fun b hb _ => ⟨⟨b, hb⟩, rfl⟩
  have hEab : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨b₁, hab⟩ := a.2
      obtain ⟨b₂, hbb⟩ := b.2
      show (a : MulAut R) * b = b * a
      rw [← hab, ← hbb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian b₁.2.1 b₂.2.1)
    · obtain ⟨b, rfl⟩ := he
      rw [← map_pow]
      have h1 : b ^ 3 = 1 := Subtype.ext (hcfg.isElemAbelian.2 b b.2.1)
      rw [h1, map_one]
  have hEinn : E ≤ (MulAut.conj : R →* MulAut R).range := by
    rintro _ ⟨b, rfl⟩
    exact (hiff b (hBsU b.2.1) (hB₁N b.2)).mp (hB₁U₁ b.2)
  have hE9 : Nat.card E ≤ 9 := by
    have hB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hcfg.1.1.1.2.2.2.2.2.2.1.1.2.1
    have hBs81 : Nat.card Bs = 81 := by rw [← hBB, hB, hm4]; norm_num
    have hB₁lt : Nat.card B₁ < 81 := by
      rw [← hBs81]
      refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left) fun heq => hcfg.2.2.1.1 ?_
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : B₁ ≤ Bs) heq.ge
      rw [this]
      exact hcfg.x_mem
    have hB₁p : IsPGroup 3 B₁ := fun g => ⟨1, by
      rw [pow_one]; exact Subtype.ext (hcfg.isElemAbelian.2 g g.2.1)⟩
    obtain ⟨k, hk⟩ := hB₁p.exists_card_eq
    have hB₁27 : Nat.card B₁ ≤ 27 := by
      rw [hk] at hB₁lt ⊢
      have : k < 4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp
        (by simpa using hB₁lt)
      interval_cases k <;> norm_num
    have hdker : (⟨d, hcfg.d_mem⟩ : B₁) ∈ β.ker := by
      have h := ggLAut_of_mem_centralizer_outdiag K θ (hcfg.d_mem_V.2)
      exact h
    have hker3 : 3 ≤ Nat.card β.ker := by
      have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hdker)
      have h2 : orderOf (⟨d, hcfg.d_mem⟩ : B₁) = 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime hcfg.d_pow hcfg.d_ne
      rwa [Nat.card_zpowers, h2] at h1
    have hcard : Nat.card β.ker * Nat.card E = Nat.card B₁ := Subgroup.card_ker_mul_card_range β
    by_contra hlt
    push Not at hlt
    have : 3 * 10 ≤ Nat.card β.ker * Nat.card E := Nat.mul_le_mul hker3 hlt
    omega
  set φ : MulAut R := ggLAut K θ ⟨x, hxN⟩ with hφdef
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hcfg.x_pow)
    rw [hφdef, ← map_pow, h1, map_one]
  have hφInn : φ ∉ (MulAut.conj : R →* MulAut R).range := fun h => hxU₁ ((hiff x hxU hxN).mpr h)
  have hφuf : ∃ u ∈ LargeEvenInnSet R, ∃ f ∈ Subgroup.closure F, φ = u * f :=
    hgrθ x hcfg.x_mem
  have hEφ : ∀ e ∈ E, e * φ = φ * e := by
    rintro _ ⟨b, rfl⟩
    show ggLAut K θ ⟨b, hB₁N b.2⟩ * ggLAut K θ ⟨x, hxN⟩ =
      ggLAut K θ ⟨x, hxN⟩ * ggLAut K θ ⟨b, hB₁N b.2⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian b.2.1 hcfg.x_mem)
  obtain ⟨r, hr3, hrE, hrφ, hrnot⟩ := hEnl hs hna φ hφ3 hφInn hφuf E hEab hEinn hE9 hEφ
  have hr3' : r ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    apply hinj
    rw [map_pow, hr3, map_one]
  obtain ⟨k, hkp, hkr⟩ := L45RankX.exists_lift_of_coprime (θ := θ) hp hZK hr3'
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hρk : ggLAut K θ ⟨k, hkN⟩ = MulAut.conj r := by
    rw [← hkr]
    exact ggLAut_mk_self K θ k
  have hkp' : (k : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hkp
  have hcomm : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)),
      ggLAut K θ ⟨g, hg⟩ * MulAut.conj r = MulAut.conj r * ggLAut K θ ⟨g, hg⟩ →
      g ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
    intro g hg h
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine commute_of_ggLAut_commute (θ := θ) hKp hZK k.2 hkp' hg ?_
    rw [hρk]
    exact h
  have hB₁k : B₁ ≤ Subgroup.centralizer ({(k : G)} : Set G) :=
    fun b hb => hcomm b (hB₁N hb) (hrE _ (hEmem b hb (hB₁N hb))).symm
  have hxk : x ∈ Subgroup.centralizer ({(k : G)} : Set G) := hcomm x hxN hrφ.symm
  have hBsk : Bs ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
    rw [hcfg.2.2.1.2]
    exact sup_le hB₁k (Subgroup.zpowers_le.mpr hxk)
  have hkC : (k : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBsk hb)
  have hkBs : (k : G) ∈ Bs := hcfg.bstar_max k hkC hkp'
  have hkU₁ : (k : G) ∈ U₁ := (hiff k (hBsU hkBs) hkN).mpr (by rw [hρk]; exact ⟨r, rfl⟩)
  have hkB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hkBs, hkU₁⟩
  exact hrnot (hρk ▸ hEmem k hkB₁ hkN)

theorem ggL45CyclicD4Input_of_enlarge (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hgr : GGNbrGraphInput) (hKG : GGD4FieldEnlargeEInput)
    (hZ : GGD4CentreThreeInput) : GGL45CyclicD4Input :=
  ggL45CyclicD4Input_of_proper hraw hiso hcent
    (ggL45D4BstarProperInput_of_enlarge hraw hiso hgr hKG hZ)

end CFSG.StandardType
