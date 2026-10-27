module

public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof
public import CFSG.RankThree.PartTwo.Sec10.Item1012ResProofTools
public import CFSG.RankThree.PartTwo.Sec10.Item1012ResProofSL2
import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofAut
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec9.NormalizerL
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsU

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1012ResProof

section General

variable {G : Type} [Group G]

theorem false_of_elemAbelian_lt (hEF : partTwoE G = partTwoF G) {S : Subgroup G}
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) (hBS : B ≤ Subgroup.normalizer (S : Set G)) {y : G}
    (hy3 : y ^ 3 = 1) (hyB : ∀ b ∈ B, y * b = b * y) (hyn : y ∉ B) : False := by
  have hBE : B ∈ partTwoE G := ⟨hB, hB27, S, hS1, hS2, hBS⟩
  rw [hEF] at hBE
  have he := Sec9.isElemAbelian_sup (Sec9.isElemAbelian_zpowers hy3) hB fun u hu b hb => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left (hyB b hb) k).eq
  have hBeq := hBE.2.1 _ he le_sup_right
  apply hyn
  rw [← hBeq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end General


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem mem_zpowers_of_mem_centralizer
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {S : Subgroup G}
    (hS : S ∈ maxInvariantPiSubgroups
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2))
    (hUS : sec10U L a ≤ S) (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥)
    (hauto : Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S)) 4 ∨
      Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S))
        (alternatingGroup (Fin 6)))
    {x : G} (hx : x ∈ Subgroup.centralizer (S : Set G) ⊓
      Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G))
    (hx3 : x ^ 3 = 1) : x ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hxa
  have hEF : partTwoE G = partTwoF G := h.partTwoE_eq h.card_eq
  have hdA := h.d_mem_A hdL
  have hd3 : d ^ 3 = 1 := h.pow_three hdA
  have ha3 : a ^ 3 = 1 := h.pow_three h.a_mem
  obtain ⟨⟨hSθ, hS2', hSA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hS
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hS2'
  have hS1 : S ≠ ⊥ := by
    intro hb
    have h4 := (Sec10XSteps.sec10U_facts h).2.1
    have h1 := Subgroup.card_le_of_le (hUS.trans hb.le)
    rw [h4, Subgroup.card_bot] at h1
    norm_num at h1
  have haS : a ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _) (hSθ hs))
  have hdS : d ∉ Subgroup.centralizer (S : Set G) := by
    intro hdC
    apply hS1
    rw [eq_bot_iff, ← hSd]
    intro s hs
    exact ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdC s hs)⟩
  set H := Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) with hH
  have hmemH : ∀ y : G, y ∈ H ↔ y * a = a * y ∧ y * d = d * y := fun y =>
    Step1012ClaimProof.mem_centralizer_closure_pair_iff
  have haH : a ∈ H := (hmemH a).mpr ⟨rfl, h.comm h.a_mem hdA⟩
  have hdH : d ∈ H := (hmemH d).mpr ⟨h.comm hdA h.a_mem, rfl⟩
  have hCN : Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.centralizer_le_normalizer _
  set N₀ := H ⊓ Subgroup.normalizer (S : Set G) with hN₀
  set φ := S.normalizerMonoidHom with hφ
  set π : N₀ →* MulAut S := φ.comp (Subgroup.inclusion inf_le_right) with hπ
  have hπapp : ∀ n : N₀, π n = φ ⟨n, n.2.2⟩ := fun n => rfl
  have hπker : ∀ n : N₀, n ∈ π.ker ↔ (n : G) ∈ Subgroup.centralizer (S : Set G) := by
    intro n
    rw [MonoidHom.mem_ker, hπapp, ← MonoidHom.mem_ker, hφ, Subgroup.normalizerMonoidHom_ker,
      Subgroup.mem_subgroupOf]
  set Y := Sec4.autIn H S with hY
  have hπrange : π.range = Y := by
    ext σ
    constructor
    · rintro ⟨n, rfl⟩
      exact Sec4.mem_autIn_iff.mpr ⟨n, n.2.2, n.2.1, rfl⟩
    · intro hσ
      obtain ⟨g, hgN, hgH, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      exact ⟨⟨g, hgH, hgN⟩, rfl⟩
  have hrank : ∀ E : Subgroup N₀, E ≤ π.ker → CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E ≤ 9 := by
    intro E hEC hE
    by_contra hlt
    push Not at hlt
    have hEp : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
    obtain ⟨m, hm⟩ := hEp.exists_card_eq
    have hm3 : 3 ≤ m := by
      by_contra hm3
      have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set E' := E.map N₀.subtype with hE'
    have hE'card : Nat.card E' = 3 ^ m := by
      rw [hE', Subgroup.card_map_of_injective N₀.subtype_injective, hm]
    obtain ⟨B, hB27, -, hBE'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
      (n := 3) (H := ⊥) (L := E') (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hE'card]; exact Nat.pow_dvd_pow 3 hm3) bot_le
    have hBC : ∀ b ∈ B, b ∈ H ∧ b ∈ Subgroup.centralizer (S : Set G) := by
      intro b hb
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (hBE' hb)
      exact ⟨e.2.1, (hπker e).mp (hEC he)⟩
    have hB : CFSG.Assembly.IsElemAbelian 3 B := by
      refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
      · obtain ⟨e, he, he'⟩ := Subgroup.mem_map.mp (hBE' u.2)
        obtain ⟨f, hf, hf'⟩ := Subgroup.mem_map.mp (hBE' v.2)
        change (u : G) * v = v * u
        rw [← he', ← hf']
        exact congrArg (fun z : E => ((z : N₀) : G)) (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
      · obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (hBE' hu)
        have := hE.2 e he
        simpa using congrArg Subtype.val this
    refine false_of_elemAbelian_lt hEF hS1 hS2 hB (by rw [hB27]; norm_num)
      (fun b hb => hCN (hBC b hb).2) hd3 (fun b hb => ((hmemH b).mp (hBC b hb).1).2.symm)
      fun hdB => hdS (hBC d hdB).2
  set Yinf := inSubgroup perfectResidual Y with hYinf
  obtain ⟨k, _, _, hk4, ρ, hρg, hρc⟩ := exists_sl2_hom hauto
  set F : Subgroup (MulAut S) := ρ.range.map Yinf.subtype with hF
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k (by omega)
  have hFperf : Group.IsPerfect F := by
    have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    exact Group.IsPerfect.map _
  have hρg3 : (ρ (g3 k)) ^ 3 = 1 := by rw [← map_pow, g3_pow_three, map_one]
  have hF3 : 3 ∣ Nat.card F := by
    have hmem : (Yinf.subtype (ρ (g3 k))) ∈ F := Subgroup.mem_map_of_mem _ ⟨g3 k, rfl⟩
    have hord : orderOf (Yinf.subtype (ρ (g3 k))) = 3 := by
      refine orderOf_eq_prime (by rw [← map_pow, hρg3, map_one]) ?_
      intro h1
      exact hρg (Yinf.subtype_injective (h1.trans (map_one _).symm))
    rw [← hord, ← Subgroup.orderOf_mk _ hmem]
    exact orderOf_dvd_natCard _
  have hFcard : Nat.card F ∣ 60 := by
    rw [hF, Subgroup.card_map_of_injective Yinf.subtype_injective, ← card_sl2_of_card_four hk4,
      MonoidHom.range_eq_map]
    exact Subgroup.card_map_dvd (H := ⊤) ρ |>.trans (by rw [Subgroup.card_top])
  have hFp : ∀ P : Subgroup (MulAut S), P ≤ F → IsPGroup 3 P → Nat.card P ≤ 3 := by
    intro P hPF hP
    obtain ⟨m, hm⟩ := hP.exists_card_eq
    have hdvd : 3 ^ m ∣ 60 := hm ▸ (Subgroup.card_dvd_of_le hPF).trans hFcard
    have hm1 : m ≤ 1 := by
      by_contra hlt
      have : 3 ^ 2 ∣ 3 ^ m := Nat.pow_dvd_pow 3 (by omega)
      have := this.trans hdvd
      norm_num at this
    rw [hm]
    interval_cases m <;> norm_num
  have hFle : F ≤ (perfectResidual π.range).map π.range.subtype := by
    rw [hπrange]
    exact Subgroup.map_subtype_le _
  have hxH : x ∈ H := hx.2
  have hxN : x ∈ Subgroup.normalizer (S : Set G) := hCN hx.1
  set x₀ : N₀ := ⟨x, hxH, hxN⟩ with hx₀
  have hx₀ker : x₀ ∈ π.ker := (hπker x₀).mpr hx.1
  have hx₀3 : x₀ ^ 3 = 1 := Subtype.ext (by simpa [hx₀] using hx3)
  obtain ⟨t, ht3, htx, htF, ht1⟩ := exists_lift π hrank hFperf hF3 hFp hFle hx₀ker hx₀3
  have hdN : d ∈ Subgroup.normalizer (S : Set G) := hSA hdA
  set d₀ : N₀ := ⟨d, hdH, hdN⟩ with hd₀
  have hπd : ∀ n : N₀, π n * π d₀ = π d₀ * π n := by
    intro n
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((hmemH n).mp n.2.1).2
  have htd : π t ∉ Subgroup.zpowers (π d₀) := by
    intro htd
    obtain ⟨_, ⟨h', rfl⟩, hh'⟩ := Subgroup.mem_map.mp htF
    have hcen : ρ h' ∈ Subgroup.center Yinf := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hyY : (y : MulAut S) ∈ π.range := hπrange ▸ (Subgroup.map_subtype_le _ y.2)
      obtain ⟨n, hn⟩ := hyY
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htd
      change (y : MulAut S) * Yinf.subtype (ρ h') = Yinf.subtype (ρ h') * y
      rw [hh', ← hn, ← hj]
      exact ((Commute.zpow_right (hπd n) j)).eq
    exact ht1 (hh'.symm.trans (by rw [hρc h' hcen, map_one]))
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 h.a_ne_one
  have hda : d ∉ Subgroup.zpowers a := by
    intro hd
    exact hdS ((Subgroup.zpowers_le.mpr haS) hd)
  have hY9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
    Sec4.card_zpowers_sup_zpowers hd3 hao hda (h.comm hdA h.a_mem)
  set Y₀ := Subgroup.zpowers a ⊔ Subgroup.zpowers d with hY₀
  have hY₀e : CFSG.Assembly.IsElemAbelian 3 Y₀ :=
    Sec9.isElemAbelian_sup (Sec9.isElemAbelian_zpowers ha3) (Sec9.isElemAbelian_zpowers hd3)
      fun u hu v hv => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact (Commute.zpow_zpow (show Commute a d from h.comm h.a_mem hdA) i j).eq
  have hxY₀ : x ∉ Y₀ := by
    intro hxY
    have hle : Subgroup.zpowers a ≤ Y₀ ⊓ Subgroup.centralizer (S : Set G) :=
      le_inf le_sup_left (Subgroup.zpowers_le.mpr haS)
    have hcard : Nat.card (Y₀ ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) ≤ 3 := by
      have hdvd : Nat.card (Y₀ ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hY9]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rw [hi']
      have hi2 : i ≠ 2 := by
        rintro rfl
        have heq : Y₀ ⊓ Subgroup.centralizer (S : Set G) = Y₀ :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hi', hY9]; norm_num)
        have hdY : d ∈ Y₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
        rw [← heq] at hdY
        exact hdS hdY.2
      interval_cases i
      · norm_num
      · norm_num
      · exact absurd rfl hi2
    have heq : Subgroup.zpowers a = Y₀ ⊓ Subgroup.centralizer (S : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hao]; exact hcard)
    exact hxa (heq ▸ ⟨hxY, hx.1⟩ : x ∈ Subgroup.zpowers a)
  have hxcomm : ∀ y ∈ Y₀, x * y = y * x := by
    intro y hy
    have hYC : Y₀ ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr ((hmemH x).mp hxH).1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr ((hmemH x).mp hxH).2.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)).symm
  obtain ⟨hEe, hE27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine hx3 hxY₀ le_rfl hY9
    hY₀e.2 hxcomm
  set E := Subgroup.zpowers x ⊔ Y₀ with hE
  have hEN : E ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxN) (sup_le (Subgroup.zpowers_le.mpr (hCN haS))
      (Subgroup.zpowers_le.mpr hdN))
  have htE : ∀ e ∈ E, (t : G) * e = e * t := by
    intro e he
    have hEC : E ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
      have htH := (hmemH t).mp t.2.1
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le (Subgroup.zpowers_le.mpr ?_)
        (Subgroup.zpowers_le.mpr ?_))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val htx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr htH.1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr htH.2.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hEC he)).symm
  have htnE : (t : G) ∉ E := by
    intro htE'
    set K' : Subgroup G := ((Subgroup.zpowers (π d₀)).comap π).map N₀.subtype with hK'
    have hEK : E ≤ K' := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le (Subgroup.zpowers_le.mpr ?_)
        (Subgroup.zpowers_le.mpr ?_))
      · refine Subgroup.mem_map.mpr ⟨x₀, ?_, rfl⟩
        rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hx₀ker]
        exact Subgroup.one_mem _
      · have haN : a ∈ N₀ := ⟨haH, hCN haS⟩
        refine Subgroup.mem_map.mpr ⟨⟨a, haN⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp ((hπker ⟨a, haN⟩).mpr haS)]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_map.mpr ⟨d₀, Subgroup.mem_zpowers _, rfl⟩
    obtain ⟨n, hn, hnt⟩ := Subgroup.mem_map.mp (hEK htE')
    have hnt' : n = t := Subtype.ext hnt
    exact htd (hnt' ▸ hn)
  have ht3' : (t : G) ^ 3 = 1 := by simpa using congrArg Subtype.val ht3
  exact false_of_elemAbelian_lt hEF hS1 hS2 hEe hE27 hEN ht3' htE htnE

end Item1012ResProof

open Item1012ResProof in
theorem step1012ClaimKM3_holds :
    Step1012ClaimKM3 := by
  intro _ _ G _ _ A c L a R h d hdL _ _ S hS hUS _ hSd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hauto x hx
    hx3
  exact mem_zpowers_of_mem_centralizer h hdL hS hUS hSd hauto hx hx3

end CFSG.RankThree.PartTwo.Sec10
