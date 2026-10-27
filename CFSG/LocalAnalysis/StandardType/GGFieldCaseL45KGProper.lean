module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGCentre
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace L45KG

open CFSG.RankThree.CentralCover

variable {G : Type} [Group G] {K : Subgroup G} {R : Type} [Group R]
  {θ : K ⧸ Subgroup.center K ≃* R}

theorem ggQuotHom_conj {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K)
    (hgk : g * k * g⁻¹ ∈ K) :
    ggQuotHom θ ⟨g * k * g⁻¹, hgk⟩ = ggLAut K θ ⟨g, hg⟩ (ggQuotHom θ ⟨k, hk⟩) := by
  rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
  rfl

theorem mem_normalizer_comap [Finite G] {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {w : R}
    (hw : ggLAut K θ ⟨g, hg⟩ w = w) :
    g ∈ Subgroup.normalizer
      ((((Subgroup.zpowers w).comap (ggQuotHom θ)).map K.subtype : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun h hh => ?_
  obtain ⟨k, hk, rfl⟩ := hh
  have hgi : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hg
  have hk' : g⁻¹ * (k : G) * g⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgi k).mp k.2
  have hwi : ggLAut K θ ⟨g⁻¹, hgi⟩ w = w := by
    have e : (⟨g⁻¹, hgi⟩ : Subgroup.normalizer (K : Set G)) = (⟨g, hg⟩)⁻¹ := rfl
    rw [e, map_inv]
    conv_lhs => rw [← hw]
    rw [MulAut.inv_apply_self]
  refine ⟨⟨_, hk'⟩, ?_, by simp⟩
  have hk2 : ggQuotHom θ k ∈ Subgroup.zpowers w := hk
  show ggQuotHom θ ⟨_, hk'⟩ ∈ Subgroup.zpowers w
  rw [ggQuotHom_conj hgi k.2 hk']
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk2
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [← hj, map_zpow, hwi]

theorem five_le_twoLocalRank_of_fix [Finite G] (hKp : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K))
    (hinj : Function.Injective (MulAut.conj : R →* MulAut R))
    {x d : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hxInn : ggLAut K θ ⟨x, hxN⟩ ∉ (MulAut.conj : R →* MulAut R).range)
    (hdK : d ∈ Subgroup.centralizer (K : Set G)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hxd : x * d = d * x) {E : Subgroup R} (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEφ : ∀ e ∈ E, ggLAut K θ ⟨x, hxN⟩ e = e) {w : R} (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hwφ : ggLAut K θ ⟨x, hxN⟩ w = w) (hwE : ∀ e ∈ E, e * w = w * e) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Finite R := Finite.of_surjective θ θ.surjective
  have : Finite (MulAut R) :=
    Finite.of_injective (fun f : MulAut R => (f : R → R)) fun f g h => MulEquiv.ext (congrFun h)
  have hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  set φ := ggLAut K θ ⟨x, hxN⟩ with hφ
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ hdK
  have hρS : ∀ (g : G) (hg : g ∈ K) (hgN : g ∈ Subgroup.normalizer (K : Set G)),
      ggLAut K θ ⟨g, hgN⟩ = MulAut.conj (ggQuotHom θ ⟨g, hg⟩) :=
    fun g hg _ => ggLAut_mk_self K θ ⟨g, hg⟩
  set S : Set G := {g | ∃ hg : g ∈ K, g ^ 3 = 1 ∧ ggQuotHom θ ⟨g, hg⟩ ∈ E} with hS
  set T : Set G := S ∪ {x, d} with hT
  have hmemT : ∀ a ∈ T, a ∈ S ∨ a = x ∨ a = d := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl ha
    · rcases ha with rfl | ha
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ha)
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    rintro a ⟨ha, -, haE⟩ b ⟨hb, hb3, hbE⟩
    refine commute_of_ggLAut_commute (θ := θ) hKp hZ3 hb hb3 (Subgroup.le_normalizer ha) ?_
    have hc : Commute (ggQuotHom θ ⟨a, ha⟩) (ggQuotHom θ ⟨b, hb⟩) :=
      mul_comm_of_isElemAbelian hE haE hbE
    rw [hρS a ha, hρS b hb]
    exact (hc.map MulAut.conj).eq
  have hcommSx : ∀ a ∈ S, Commute x a := by
    rintro a ⟨ha, ha3, haE⟩
    refine commute_of_ggLAut_commute (θ := θ) hKp hZ3 ha ha3 hxN ?_
    rw [hρS a ha, D4Rank.mulAut_mul_conj, hEφ _ haE]
  have hcommSd : ∀ a ∈ S, Commute d a := fun a ha =>
    ((Subgroup.mem_centralizer_iff.mp hdK) a ha.1).symm
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, Commute a b := by
    intro a ha b hb
    rcases hmemT a ha with ha' | ha' | ha' <;> rcases hmemT b hb with hb' | hb' | hb'
    · exact hcommS a ha' b hb'
    · rw [hb']; exact (hcommSx a ha').symm
    · rw [hb']; exact (hcommSd a ha').symm
    · rw [ha']; exact hcommSx b hb'
    · simp only [ha', hb', Commute.refl]
    · rw [ha', hb']; exact hxd
    · rw [ha']; exact hcommSd b hb'
    · rw [ha', hb']; exact hxd.symm
    · simp only [ha', hb', Commute.refl]
  have hpowT : ∀ a ∈ T, a ^ 3 = 1 := by
    intro a ha
    rcases hmemT a ha with ha | rfl | rfl
    · exact ha.2.1
    · exact hx3
    · exact hd3
  set A : Subgroup G := Subgroup.closure T with hA
  have hAel : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => pow_eq_one_of_mem_closure hcommT hpowT ha⟩
    show (a : G) * b = b * a
    exact (commute_of_mem_closure hcommT a.2 b.2).eq
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro a ha
    rcases hmemT a ha with ha | rfl | rfl
    · exact Subgroup.le_normalizer ha.1
    · exact hxN
    · exact hdN
  have hdA : d ∈ A := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hxA : x ∈ A := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  set β : A →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hAN) with hβ
  have hdker : (⟨d, hdA⟩ : A) ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    exact ggLAut_eq_one_of_mem_centralizer K θ (g := ⟨d, hAN hdA⟩) hdK
  have hker3 : 3 ≤ Nat.card β.ker := by
    have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hdker)
    have h2 : orderOf (⟨d, hdA⟩ : A) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    rwa [Nat.card_zpowers, h2] at h1
  set cE : Subgroup (MulAut R) := E.map (MulAut.conj : R →* MulAut R) with hcE
  have hcEr : cE ≤ β.range := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨k, hk3, hke⟩ := L45RankX.exists_lift_of_coprime (θ := θ) hp3 hZ3 (r := e) (m := 1)
      (by rw [pow_one]; exact hE.2 e he)
    have hk3' : (k : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hk3
    have hq : ggQuotHom θ ⟨(k : G), k.2⟩ = e := by
      rw [ggQuotHom_apply]
      exact hke
    have hkS : (k : G) ∈ S := ⟨k.2, hk3', by rw [hq]; exact he⟩
    have hkA : (k : G) ∈ A := Subgroup.subset_closure (Or.inl hkS)
    refine ⟨⟨k, hkA⟩, ?_⟩
    show ggLAut K θ ⟨(k : G), hAN hkA⟩ = MulAut.conj e
    rw [hρS _ k.2, hq]
  have hφr : φ ∈ β.range := ⟨⟨x, hxA⟩, rfl⟩
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [hφ, ← map_pow, h1, map_one]
  have hφ1 : φ ≠ 1 := fun h => hxInn (h ▸ one_mem _)
  have hφo : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hcEcard : Nat.card cE = 27 := by
    rw [hcE, Subgroup.card_map_of_injective hinj, hE27]
  have hφcomm : ∀ c ∈ cE, c * φ = φ * c := by
    rintro _ ⟨e, he, rfl⟩
    rw [D4Rank.mulAut_mul_conj, hEφ e he]
  have hnorm : Subgroup.zpowers φ ≤ Subgroup.normalizer (cE : Set (MulAut R)) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun c hc => hφcomm c hc))
  have hdisj : Disjoint cE (Subgroup.zpowers φ) := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ hc
    by_contra hne
    have hle : Subgroup.zpowers (MulAut.conj e) ≤ Subgroup.zpowers φ :=
      Subgroup.zpowers_le.mpr hc
    have he3 : (MulAut.conj e) ^ 3 = 1 := by rw [← map_pow, hE.2 e he, map_one]
    have ho : orderOf (MulAut.conj e) = 3 := orderOf_eq_prime he3 hne
    have heq : Subgroup.zpowers (MulAut.conj e) = Subgroup.zpowers φ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ho, hφo])
    have hφm : φ ∈ Subgroup.zpowers (MulAut.conj e) := heq ▸ Subgroup.mem_zpowers φ
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hφm
    exact hxInn ⟨e ^ m, by rw [map_zpow, hm]⟩
  have hsup : Nat.card (cE ⊔ Subgroup.zpowers φ : Subgroup (MulAut R)) = 81 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      hcEcard, Nat.card_zpowers, hφo]
  have hrange : 81 ≤ Nat.card β.range := by
    rw [← hsup]
    exact Subgroup.card_le_of_le (sup_le hcEr (Subgroup.zpowers_le.mpr hφr))
  have hcardA : 3 ^ 5 ≤ Nat.card A := by
    calc 3 ^ 5 = 3 * 81 := by norm_num
      _ ≤ Nat.card β.ker * Nat.card β.range := Nat.mul_le_mul hker3 hrange
      _ = Nat.card A := Subgroup.card_ker_mul_card_range β
  set W : Subgroup G := ((Subgroup.zpowers w).comap (ggQuotHom θ)).map K.subtype with hW
  have hW2 : IsPGroup 2 W := by
    refine IsPGroup.map ?_ K.subtype
    refine IsPGroup.comap_of_ker_isPGroup ?_ (ggQuotHom θ) ?_
    · intro g
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hj, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
    · rw [ker_ggQuotHom]
      exact hZ2
  have hW1 : W ≠ ⊥ := by
    obtain ⟨k, hk⟩ := ggQuotHom_surjective θ w
    intro hbot
    have hkW : (k : G) ∈ W := ⟨k, show ggQuotHom θ k ∈ Subgroup.zpowers w by
      rw [hk]; exact Subgroup.mem_zpowers w, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hkW
    have hk1 : k = 1 := Subtype.ext hkW
    rw [hk1, map_one] at hk
    exact hw1 hk.symm
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro a ha
    rcases hmemT a ha with ⟨haK, -, haE⟩ | ha' | ha'
    · refine mem_normalizer_comap (Subgroup.le_normalizer haK) ?_
      rw [hρS _ haK, MulAut.conj_apply, hwE _ haE, mul_inv_cancel_right]
    · rw [ha']
      exact mem_normalizer_comap hxN hwφ
    · rw [ha']
      refine mem_normalizer_comap hdN ?_
      rw [ggLAut_eq_one_of_mem_centralizer K θ (g := ⟨d, hdN⟩) hdK, MulAut.one_apply]
  have hTL : IsTwoLocal (Subgroup.normalizer (W : Set G)) := ⟨W, hW1, hW2, rfl⟩
  have hle := TableB.card_le_of_twoLocal hp3 hTL hAW hAel
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hcardA.trans hle)

end L45KG

@[expose] def GGD4FieldFixLocal : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ φ : MulAut R, φ ^ 3 = 1 → φ ∉ (MulAut.conj : R →* MulAut R).range →
      (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) →
      ∃ (E : Subgroup R) (w : R), IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ (∀ e ∈ E, φ e = e) ∧
        w ^ 2 = 1 ∧ w ≠ 1 ∧ φ w = w ∧ ∀ e ∈ E, e * w = w * e

@[expose] def GGD4FieldFixLocalOddInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .D → lab.rank = 4 → Odd lab.n →
    LargeEvenLabelAll lab GGD4FieldFixLocal

section Certs


theorem ggL45D4BstarProperInput_of_fixLocal (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hgr : GGNbrGraphInput) (hKG : GGD4FieldFixLocalOddInput) :
    GGL45D4BstarProperInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hp3 hmk hm4 _
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmk' : LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ 4 ≤ lab.rank) := by
    obtain ⟨hperf, lab, hlab, hraw0⟩ := hmk
    exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, ht, h4⟩ => ⟨hs, hna, θ, ht, h4.ge⟩) hraw0⟩
  have hZ2 : IsPGroup 2 (Subgroup.center K) := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card (Subgroup.center K)) with
      ⟨k, hk⟩ | ⟨q, hq, hqd, hqo⟩
    · exact IsPGroup.of_card hk
    · exfalso
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hqo) even_two
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp
        (coprime_card_center_of_marking_omegaPlus hq hq2 hmk') hqd
  have hUK := hcfg.le_normalizer
  have hBsU := hcfg.bs_le
  have hKp : commutator K = ⊤ := hcfg.2.2.2.2.2.2.2.1.2.2.1
  obtain ⟨-, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hxU : x ∈ U := hBsU hcfg.x_mem
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hUK hxU
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := fun b hb => hUK (hBsU hb)
  have hdK : d ∈ Subgroup.centralizer (K : Set G) := hcfg.d_mem_V.2
  have hd3 : d ^ 3 = 1 := hcfg.d_pow
  have hd1 : d ≠ 1 := hcfg.d_ne
  have hxd : x * d = d * x :=
    mul_comm_of_isElemAbelian hcfg.isElemAbelian hcfg.x_mem hcfg.d_mem.1
  have hM1 := hgr G 3 B Bs x L D J hcfg.1.1 y K hcfg.2.2.2.2.2.1.2.2.1 hN _ hmk
  have hM3 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField 3)
    (fun lab hl _ => hraw 3 hp (by norm_num) lab hl) (fun _ _ _ _ _ _ _ => trivial) hM1
  have hM4 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := GGRawInndiagIso) (fun lab hl _ => hiso lab hl) (fun _ _ _ _ _ _ _ => trivial) hM3
  obtain ⟨-, lab₁, hlab₁, hraw₁⟩ := hM4
  obtain ⟨-, _, -, -, -, -, -, ⟨⟨⟨ht, h4⟩, -⟩, -⟩, -⟩ := largeEvenRawDatum_exists hraw₁
  have hall : LargeEvenLabelAll lab₁ fun R _ I _ => I = LargeEvenInnSet R ∧
      (3 ∣ 2 ^ lab₁.n - 1 → GGTorusLift 3 4 R) :=
    largeEvenLabelAll_omegaPlus ht (by omega) fun 𝔽 _ _ _ h𝔽 => ⟨rfl, fun h3 => by
      rw [h4]
      exact TableBSymp.ggTorusLift_omegaPlus hp (by norm_num) (by rw [h𝔽]; exact h3)
        (by norm_num)⟩
  rcases Nat.even_or_odd lab₁.n with hev | hodd
  ·
    have h3 : 3 ∣ 2 ^ lab₁.n - 1 := by
      obtain ⟨m, hm⟩ := hev
      have h := Nat.sub_dvd_pow_sub_pow 4 1 m
      rw [one_pow, show (4 : ℕ) - 1 = 3 by norm_num,
        show (4 : ℕ) ^ m = 2 ^ (m + m) by rw [← two_mul, pow_mul]; norm_num] at h
      rw [hm]
      exact h
    obtain ⟨R, _, I, F, ⟨-, -, θ, -⟩, -, hTL⟩ := largeEvenRawDatum_exists (hall _ hraw₁)
    have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hdK) k hk)
    have h5 := succ_le_twoLocalRank_of_torusLift hp hKd hd3 hd1 hKp θ (hTL h3)
    omega
  ·
    obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, ⟨⟨⟨-, hgrθ⟩, hRIF⟩, hisoR⟩⟩, hI, -⟩, hFix⟩ :=
      largeEvenRawDatum_exists (hKG lab₁ hlab₁ ht h4 hodd _ (hall _ hraw₁))
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
    have hφ3 : ggLAut K θ ⟨x, hxN⟩ ^ 3 = 1 := by
      have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hcfg.x_pow)
      rw [← map_pow, h1, map_one]
    have hφInn : ggLAut K θ ⟨x, hxN⟩ ∉ (MulAut.conj : R →* MulAut R).range :=
      fun h => hxU₁ ((hiff x hxU hxN).mpr h)
    obtain ⟨E, w, hE, hE27, hEφ, hw2, hw1, hwφ, hwE⟩ :=
      hFix hs hna _ hφ3 hφInn (hgrθ x hcfg.x_mem)
    have h5 := L45KG.five_le_twoLocalRank_of_fix hKp hZ2 hinj hxN hcfg.x_pow hφInn hdK hd3 hd1
      hxd hE hE27 hEφ hw2 hw1 hwφ hwE
    omega

theorem ggL45CyclicD4Input_of_fixLocal (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hgr : GGNbrGraphInput) (hKG : GGD4FieldFixLocalOddInput) :
    GGL45CyclicD4Input :=
  ggL45CyclicD4Input_of_proper hraw hiso hcent
    (ggL45D4BstarProperInput_of_fixLocal hraw hiso hgr hKG)

end Certs

end CFSG.StandardType
