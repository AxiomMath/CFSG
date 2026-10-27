module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofApply
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofLocalRank
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item812Res7

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
def trivModSub (W M : Subgroup G) (hWM : W ≤ Subgroup.normalizer (M : Set G)) (S : Set G) :
    Subgroup G where
  carrier := {f | f ∈ W ∧ ∀ g ∈ S, f * g * f⁻¹ * g⁻¹ ∈ M}
  mul_mem' := by
    rintro f₁ f₂ ⟨hf₁W, hf₁⟩ ⟨hf₂W, hf₂⟩
    refine ⟨W.mul_mem hf₁W hf₂W, fun g hg => ?_⟩
    have h1 : f₁ * (f₂ * g * f₂⁻¹ * g⁻¹) * f₁⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hWM hf₁W) _).mp (hf₂ g hg)
    have e : f₁ * f₂ * g * (f₁ * f₂)⁻¹ * g⁻¹ =
        (f₁ * (f₂ * g * f₂⁻¹ * g⁻¹) * f₁⁻¹) * (f₁ * g * f₁⁻¹ * g⁻¹) := by group
    rw [e]
    exact M.mul_mem h1 (hf₁ g hg)
  one_mem' := ⟨W.one_mem, fun g _ => by simp⟩
  inv_mem' := by
    rintro f ⟨hfW, hf⟩
    refine ⟨W.inv_mem hfW, fun g hg => ?_⟩
    have h1 : f⁻¹ * (f * g * f⁻¹ * g⁻¹)⁻¹ * f⁻¹⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hWM (W.inv_mem hfW)) _).mp (M.inv_mem (hf g hg))
    have e : f⁻¹ * g * f⁻¹⁻¹ * g⁻¹ = f⁻¹ * (f * g * f⁻¹ * g⁻¹)⁻¹ * f⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem normalizer_le_normalizer_theta (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (((aschbacherSolvableCore 3 ↥J).map J.subtype : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_of_conj_mem fun _ ht =>
    CFSG.RankThree.GroupTheory.conj_mem_inSubgroup_aschbacherSolvableCore hg ht

theorem isSolvable_theta (J : Subgroup G) :
    Group.IsSolvable ((aschbacherSolvableCore 3 ↥J).map J.subtype : Subgroup G) := by
  have := (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).1
  exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective
    (aschbacherSolvableCore 3 ↥J) J.subtype J.subtype_injective).toMonoidHom)
    (MulEquiv.surjective _)

theorem not_three_dvd_card_theta (J : Subgroup G) :
    ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥J).map J.subtype : Subgroup G) := by
  rw [Subgroup.card_map_of_injective J.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).2.2.1

theorem false_of_trivial_quot (h3 : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3)
    {J F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hFJ : F ≤ Subgroup.normalizer (J : Set G))
    (hFtriv : ∀ f ∈ F, ∀ j ∈ J,
      f * j * f⁻¹ * j⁻¹ ∈ ((aschbacherSolvableCore 3 ↥J).map J.subtype : Subgroup G))
    {y : ↥J ⧸ aschbacherSolvableCore 3 ↥J} {T : Subgroup (↥J ⧸ aschbacherSolvableCore 3 ↥J)}
    (hy3 : y ^ 3 = 1) (hyZ : y ∉ Subgroup.center (↥J ⧸ aschbacherSolvableCore 3 ↥J))
    (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hyT : y ∈ Subgroup.normalizer (T : Set _)) : False := by
  classical
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥J) y
  set θJ := aschbacherSolvableCore 3 ↥J with hθJ
  set π := QuotientGroup.mk' θJ with hπ
  set N : Subgroup G := θJ.map J.subtype with hN
  set D : Subgroup G := (T.comap π).map J.subtype with hD
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_theta J
  have hFN : F ≤ Subgroup.normalizer (N : Set G) := hFJ.trans (normalizer_le_normalizer_theta J)
  have hyN : (y₀ : G) ∈ Subgroup.normalizer (N : Set G) :=
    normalizer_le_normalizer_theta J (Subgroup.le_normalizer y₀.2)
  have hπ1 : ∀ t : ↥J, t ∈ θJ ↔ π t = 1 := fun t => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hy3' : (y₀ : G) ^ 3 ∈ N := by
    refine ⟨y₀ ^ 3, (hπ1 _).mpr ?_, by simp⟩
    rw [map_pow]
    exact hy3
  have hFy : ∀ f ∈ F, (y₀ : G)⁻¹ * (f * y₀ * f⁻¹) ∈ N := by
    intro f hf
    have h1 := hFtriv f hf y₀ y₀.2
    have h2 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyN) _).mp h1
    have e : (y₀ : G)⁻¹ * (f * y₀ * f⁻¹) =
        (y₀ : G)⁻¹ * (f * y₀ * f⁻¹ * (y₀ : G)⁻¹) * (y₀ : G)⁻¹⁻¹ := by group
    rw [e]
    exact h2
  have hyF : ∀ f ∈ F, ∀ m ∈ N, (y₀ : G) ≠ f * m := by
    rintro f hf _ ⟨m₀, hm₀, rfl⟩ hyfm
    have hfJ : f ∈ J := by
      have e : f = (y₀ : G) * ((m₀ : ↥J) : G)⁻¹ := by
        rw [hyfm]
        simp
      rw [e]
      exact J.mul_mem y₀.2 (J.inv_mem m₀.2)
    set f₀ : ↥J := ⟨f, hfJ⟩ with hf₀
    have hyf₀ : y₀ = f₀ * m₀ := Subtype.ext (by simpa using hyfm)
    have hπf : π f₀ = π y₀ := by
      rw [hyf₀, map_mul, (hπ1 m₀).mp hm₀, mul_one]
    apply hyZ
    rw [← hπf, Subgroup.mem_center_iff]
    intro z
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective θJ z
    obtain ⟨t, ht, hte⟩ := hFtriv f hf j j.2
    have ht' : t = f₀ * j * f₀⁻¹ * j⁻¹ := by
      apply Subtype.ext
      have h1 : (t : G) = f * (j : G) * f⁻¹ * (j : G)⁻¹ := hte
      rw [h1]
      simp [hf₀]
    have hπt : π (f₀ * j * f₀⁻¹ * j⁻¹) = 1 := ht' ▸ (hπ1 t).mp ht
    simp only [map_mul, map_inv] at hπt
    have h1 : π f₀ * π j * (π f₀)⁻¹ = π j := mul_inv_eq_one.mp hπt
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hND : N ≤ D := by
    rintro _ ⟨m₀, hm₀, rfl⟩
    refine ⟨m₀, ?_, rfl⟩
    change π m₀ ∈ T
    rw [(hπ1 m₀).mp hm₀]
    exact T.one_mem
  have hDcard : Nat.card D = Nat.card θJ * Nat.card T := by
    rw [hD, Subgroup.card_map_of_injective J.subtype_injective]
    exact QuotientGroup.card_preimage_mk θJ (T : Set (↥J ⧸ θJ))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hT2' : 2 ∣ Nat.card T := by
    rcases hT2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.eq_bot_of_card_eq T h1) hT1
    · exact h2
  have hD3 : ¬ 3 ∣ Nat.card D := by
    rw [hDcard]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact (solvable_prime_complement_core_characterization (H := ↥J)
        Nat.prime_three).2.2.1 h
    · rw [hk] at h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  have hD2 : 2 ∣ Nat.card D := by
    rw [hDcard]
    exact Dvd.dvd.mul_left hT2' _
  have hFD : F ≤ Subgroup.normalizer (D : Set G) := by
    intro f hf
    refine mem_normalizer_of_conj_mem fun _ hd => ?_
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have h1 : f * (d₀ : G) * f⁻¹ * (d₀ : G)⁻¹ ∈ D := hND (hFtriv f hf d₀ d₀.2)
    have h2 : (d₀ : G) ∈ D := ⟨d₀, hd₀, rfl⟩
    have e : f * (d₀ : G) * f⁻¹ = f * (d₀ : G) * f⁻¹ * (d₀ : G)⁻¹ * d₀ := by group
    show f * (d₀ : G) * f⁻¹ ∈ D
    rw [e]
    exact D.mul_mem h1 h2
  have hyD : (y₀ : G) ∈ Subgroup.normalizer (D : Set G) := by
    refine mem_normalizer_of_conj_mem fun _ hd => ?_
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    refine ⟨y₀ * d₀ * y₀⁻¹, ?_, by simp⟩
    change π (y₀ * d₀ * y₀⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hyT _).mp hd₀
  have h4 := four_le_localRank_of_trivial_mod hF hF27 hN3 hFN hyN hy3' hFy hyF hND hD3 hD2 hFD
    hyD
  omega

theorem sec8I_le (L : Subgroup G) (a : G) :
    sec8I L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := by
  unfold sec8I
  split_ifs
  · exact (Subgroup.closure_le _).mpr fun y hy => hy.1
  · exact Subgroup.map_subtype_le _

theorem mem_normalizer_sec8I {L : Subgroup G} {a d : G}
    (hd : d ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G)) :
    d ∈ Subgroup.normalizer (sec8I L a : Set G) := by
  unfold sec8I
  split_ifs
  · refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hle : Subgroup.closure {y | y ∈ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
          ∃ k : ℕ, y ^ 2 ^ k = 1} ≤
        (Subgroup.closure {y | y ∈ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
          ∃ k : ℕ, y ^ 2 ^ k = 1}).comap (MulAut.conj d).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ⟨hy, k, hk⟩
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hd y).mp hy, k, ?_⟩
      change (d * y * d⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hk]
      group
    exact hle hp
  · exact Item812Res2.mem_normalizer_inSubgroup_perfectResidual hd

end Tools

end Item812Res7

section Final

open Item812Res7

@[expose] def KF89JTwoLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∃ (y : ↥(sec8J X a) ⧸ aschbacherSolvableCore 3 ↥(sec8J X a))
      (T : Subgroup (↥(sec8J X a) ⧸ aschbacherSolvableCore 3 ↥(sec8J X a))),
      y ^ 3 = 1 ∧ y ∉ Subgroup.center (↥(sec8J X a) ⧸ aschbacherSolvableCore 3 ↥(sec8J X a)) ∧
        T ≠ ⊥ ∧ IsPGroup 2 T ∧ y ∈ Subgroup.normalizer (T : Set _)

@[expose] def KF89BNotCentI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∃ i ∈ sec8I L a, b * i * b⁻¹ * i⁻¹ ∉
      ((aschbacherSolvableCore 3 ↥(sec8I L a)).map (sec8I L a).subtype : Subgroup G)

theorem kF89JCentA_of (h45 : Sec4.Item4_5) (h84 : Pair84A) (hJ : KF89JTwoLocal)
    (hI : KF89BNotCentI) : KF89JCentA := by
  intro G _ _ A c L a b X n h Y₀ hY₀ hIJ x hxA hx
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ΘH : Subgroup G := (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))).map
    (Subgroup.centralizer ({a} : Set G)).subtype with hΘH
  set Y : Subgroup G := Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype with hYdef
  have h3 : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 :=
    h.toTheoremFourHyp.localRank_three.le
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAab.2 c hcA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAC : ∀ {e : G}, e ∈ A → A ≤ Subgroup.centralizer ({e} : Set G) := fun he u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu _ he)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hAp
      (hAC hbA) X h.pairRel.2.2.1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 hc1 hAp
      (hAC hcA) L h.mem_thetaComponentsAt
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) := hAC haA
  have hAHn : A ≤ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
    hAH.trans Subgroup.le_normalizer
  have hAJ : A ≤ Subgroup.normalizer (sec8J X a : Set G) := fun u hu =>
    Item812Res2.mem_normalizer_inSubgroup_perfectResidual (Late.le_normalizer_inf hAX hAHn hu)
  have hAI : A ≤ Subgroup.normalizer (sec8I L a : Set G) := fun u hu =>
    mem_normalizer_sec8I (Late.le_normalizer_inf hAL hAHn hu)
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := by
    obtain ⟨X', -, hX'⟩ := h.pairRel.2.2.1
    rw [← hX']
    exact Subgroup.map_subtype_le X'
  have hJXa : sec8J X a ≤ X ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hIL : sec8I L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := sec8I_le L a
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hxY : ∀ g ∈ Y, (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈ ΘH := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hx y hy, by simp⟩
  have hHΘ : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (ΘH : Set G) :=
    fun g hg => normalizer_le_normalizer_theta (Subgroup.centralizer ({a} : Set G))
      (Subgroup.le_normalizer hg)
  have hΘs : Group.IsSolvable ΘH := isSolvable_theta (Subgroup.centralizer ({a} : Set G))
  have hΘ3 : ¬ 3 ∣ Nat.card ΘH := not_three_dvd_card_theta (Subgroup.centralizer ({a} : Set G))
  have hba : b ∉ Subgroup.zpowers a := by
    intro hbk
    have hab : a ∈ Subgroup.zpowers b := by
      have hle : Subgroup.zpowers b ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).mpr hbk
      have heq : Subgroup.zpowers b = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1,
            orderOf_eq_prime hb3 hb1])
      rw [heq]
      exact Subgroup.mem_zpowers a
    have hout : Sec4.InducesOuterTheta a X := by
      rcases h84 G A c L a b X n h with h' | h'
      · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    obtain ⟨haN, hnot⟩ := hout
    apply hnot
    have hay : ∀ y ∈ X, a * y = y * a := by
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hab
      have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (hXb hy)
      exact (Commute.zpow_left (show Commute b y from hyb.symm) j).eq
    rw [KFacts.thetaQuotMulAut_compAction_eq_one haN hay]
    exact ⟨1, map_one _⟩
  have hab9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = 3 ^ 2 :=
    Item812Res3.card_sup_zpowers_eq_sq Nat.prime_three ha3 ha1 hb3 hba (hAc a haA b hbA)
  have hEA : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ A :=
    sup_le ((Subgroup.zpowers_le).mpr haA) ((Subgroup.zpowers_le).mpr hbA)
  have hxab : (x : G) ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    by_contra hxab
    set E := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hE
    have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
      ⟨⟨⟨fun u v => Subtype.ext (hAc u (hEA u.2) v (hEA v.2))⟩⟩, fun u hu => hAab.2 u (hEA hu)⟩
    obtain ⟨hFab, hFcard⟩ := Sec5.isElemAbelian_sup_zpowers hEab hxab (hAab.2 x hxA)
      (fun e he => hAc e (hEA he) x hxA)
    set F := E ⊔ Subgroup.zpowers (x : G) with hF
    have hF27 : Nat.card F = 27 := by rw [hFcard, hab9]; norm_num
    have hFA : F ≤ A := sup_le hEA ((Subgroup.zpowers_le).mpr hxA)
    set θJ : Subgroup G := (aschbacherSolvableCore 3 ↥(sec8J X a)).map (sec8J X a).subtype
      with hθJ
    have hFT : F ≤ trivModSub (Subgroup.normalizer (sec8J X a : Set G)) θJ
        (normalizer_le_normalizer_theta _) (sec8J X a : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · refine (Subgroup.zpowers_le).mpr ⟨hAJ haA, fun g hg => ?_⟩
        have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hJXa hg).2
        rw [← hga]
        simp
      · refine (Subgroup.zpowers_le).mpr ⟨hAJ hbA, fun g hg => ?_⟩
        have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp (hXb (hJXa hg).1)
        rw [← hgb]
        simp
      · refine (Subgroup.zpowers_le).mpr ⟨hAJ hxA, fun g hg => ?_⟩
        refine Sec15.inf_le_map_aschbacherSolvableCore ((hJXa.trans inf_le_right).trans hHΘ)
          hΘs hΘ3 ⟨hxY g (hJY hg), ?_⟩
        have hxg : (x : G) * g * (x : G)⁻¹ ∈ sec8J X a :=
          (Subgroup.mem_normalizer_iff.mp (hAJ hxA) g).mp hg
        exact (sec8J X a).mul_mem hxg ((sec8J X a).inv_mem hg)
    obtain ⟨yb, T, hy3, hyZ, hT1, hT2, hyT⟩ := hJ G A c L a b X n h
    exact false_of_trivial_quot h3 hFab hF27 (fun f hf => (hFT hf).1)
      (fun f hf => (hFT hf).2) hy3 hyZ hT1 hT2 hyT
  by_contra hxa
  have hax9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers (x : G) : Subgroup G) = 3 ^ 2 :=
    Item812Res3.card_sup_zpowers_eq_sq Nat.prime_three ha3 ha1 (hAab.2 x hxA) hxa
      (hAc a haA x hxA)
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers (x : G) ≤
      Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    sup_le le_sup_left ((Subgroup.zpowers_le).mpr hxab)
  have heq : Subgroup.zpowers a ⊔ Subgroup.zpowers (x : G) =
      Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hax9, hab9])
  have hbax : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers (x : G) :=
    heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hTsub : Subgroup.zpowers a ⊔ Subgroup.zpowers (x : G) ≤
      trivModSub (Subgroup.centralizer ({a} : Set G)) ΘH hHΘ (Y : Set G) := by
    refine sup_le ((Subgroup.zpowers_le).mpr ⟨hAH haA, fun g hg => ?_⟩)
      ((Subgroup.zpowers_le).mpr ⟨x.2, hxY⟩)
    have hga : g * a = a * g := (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.map_subtype_le Y₀ hg))
    rw [← hga]
    simp
  have hbT := hTsub hbax
  obtain ⟨i, hiI, hi⟩ := hI G A c L a b X n h
  apply hi
  refine Sec15.inf_le_map_aschbacherSolvableCore ((hIL.trans inf_le_right).trans hHΘ)
    hΘs hΘ3 ⟨hbT.2 i (hIY hiI), ?_⟩
  have hbi : b * i * b⁻¹ ∈ sec8I L a := (Subgroup.mem_normalizer_iff.mp (hAI hbA) i).mp hiI
  exact (sec8I L a).mul_mem hbi ((sec8I L a).inv_mem hiI)

end Final

end CFSG.RankThree.PartTwo.Sec8
