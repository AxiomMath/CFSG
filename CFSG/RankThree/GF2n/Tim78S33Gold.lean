module

public import CFSG.RankThree.GF2n.Tim78S32
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def GoldschmidtInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X), A ≤ S →
    IsMulCommutative A →
    (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) →
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓
      CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
      CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K)

theorem inv_of_fpf {X : Subgroup G} {c : G} (hc : c * c = 1)
    (hcX : c ∈ Subgroup.normalizer (X : Set G)) (hfix : ∀ x ∈ X, c * x = x * c → x = 1) :
    ∀ z ∈ X, c * z * c⁻¹ = z⁻¹ := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcm : ∀ x ∈ X, c * x * c⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.mp hcX x).mp hx
  let f : ↥X → ↥X := fun x =>
    ⟨(x : G)⁻¹ * (c * x * c⁻¹), X.mul_mem (X.inv_mem x.2) (hcm x x.2)⟩
  have hf : Function.Injective f := by
    intro x y h
    have h1 : (x : G)⁻¹ * (c * x * c⁻¹) = (y : G)⁻¹ * (c * y * c⁻¹) := congrArg Subtype.val h
    have e1 : c * (x : G) = (x : G) * (y : G)⁻¹ * c * y := by
      calc c * (x : G) = (x : G) * ((x : G)⁻¹ * (c * x * c⁻¹)) * c := by group
        _ = (x : G) * ((y : G)⁻¹ * (c * y * c⁻¹)) * c := by rw [h1]
        _ = (x : G) * (y : G)⁻¹ * c * y := by group
    have h2 : c * ((y : G) * (x : G)⁻¹) = ((y : G) * (x : G)⁻¹) * c := by
      symm
      calc (y : G) * (x : G)⁻¹ * c = (y : G) * (x : G)⁻¹ * (c * x) * (x : G)⁻¹ := by group
        _ = (y : G) * (x : G)⁻¹ * ((x : G) * (y : G)⁻¹ * c * y) * (x : G)⁻¹ := by rw [e1]
        _ = c * ((y : G) * (x : G)⁻¹) := by group
    have h3 := hfix _ (X.mul_mem y.2 (X.inv_mem x.2)) h2
    rw [mul_inv_eq_one] at h3
    exact Subtype.ext h3.symm
  have hsurj := Finite.injective_iff_surjective.mp hf
  intro z hz
  obtain ⟨x, hx⟩ := hsurj ⟨z, hz⟩
  have hx' : (x : G)⁻¹ * (c * x * c⁻¹) = z := congrArg Subtype.val hx
  rw [← hx']
  calc c * ((x : G)⁻¹ * (c * x * c⁻¹)) * c⁻¹ = c * (x : G)⁻¹ * c * x * (c⁻¹ * c⁻¹) := by group
    _ = c * (x : G)⁻¹ * c * x := by rw [hci, hc, mul_one]
    _ = ((x : G)⁻¹ * (c * x * c⁻¹))⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, hci]
        group

theorem eq_bot_of_fpf_klein {X : Subgroup G} {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (haX : a ∈ Subgroup.normalizer (X : Set G)) (hbX : b ∈ Subgroup.normalizer (X : Set G))
    (hfa : ∀ x ∈ X, a * x = x * a → x = 1) (hfb : ∀ x ∈ X, b * x = x * b → x = 1)
    (hfab : ∀ x ∈ X, a * b * x = x * (a * b) → x = 1) : X = ⊥ := by
  have hia := inv_of_fpf ha haX hfa
  have hib := inv_of_fpf hb hbX hfb
  rw [eq_bot_iff]
  intro z hz
  refine hfab z hz ?_
  have h1 := hia _ (X.inv_mem hz)
  have h2 := hib z hz
  calc a * b * z = a * (b * z * b⁻¹) * b := by group
    _ = a * z⁻¹ * b := by rw [h2]
    _ = (a * z⁻¹ * a⁻¹) * (a * b) := by group
    _ = z * (a * b) := by rw [h1, inv_inv]

omit [Finite G] in
theorem exists_ne_ne_of_four_le {V : Subgroup G} [Finite V] (h4 : 4 ≤ Nat.card V) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hinj : Function.Injective (fun z : ↥V => decide ((z : G) = 1)) := by
    intro z z' h
    by_cases hz : (z : G) = 1
    · have hz' : (z' : G) = 1 := by simpa [hz] using h
      exact Subtype.ext (hz.trans hz'.symm)
    · have hz' : (z' : G) ≠ 1 := by simpa [hz] using h
      exact Subtype.ext (by
        by_contra hne
        exact hne (hcon _ z.2 _ z'.2 hz hz'))
  have h2 := Nat.card_le_card_of_injective _ hinj
  have hb : Nat.card Bool = 2 := by simp
  omega

namespace S3Hyp

variable {M U : Subgroup G} (H : S3Hyp M U)
include H

omit [Finite G] in
theorem exp_ne : ∃ x ∈ U, x ^ 2 ≠ 1 := by
  obtain ⟨x, hx, hxV⟩ : ∃ x ∈ U, x ∉ PartTwo.omegaOneSub U := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact H.ne (le_antisymm (PartTwo.omegaOneSub_le U) hcon)
  exact ⟨x, hx, fun h2 => hxV ((mem_omegaOneSub_iff H.comm).mpr ⟨hx, by rw [← sq]; exact h2⟩)⟩

omit [Finite G] in
theorem setup : Setup210 U U where
  comm := H.comm
  two := H.two
  exp_ne := H.exp_ne
  ti := H.ti
  conj := ⟨1, (conjSubgroup_one U).symm⟩
  ne_bot := by
    rw [inf_of_le_left Subgroup.le_normalizer]
    intro h
    apply H.omega_ne_bot
    rw [eq_bot_iff, ← h]
    exact PartTwo.omegaOneSub_le U

theorem root (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    IsRootTypeTI (PartTwo.omegaOneSub U) :=
  (tim78_2_10_a hCen hU H.setup).2

theorem eq_bot_of_odd {N : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNQ : N ⊓ inSubgroup (pCore 2) M = ⊥ := by
    have hcop : Nat.Coprime (Nat.card N) (Nat.card ↥(inSubgroup (pCore 2) M)) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ2
      rw [hk]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hCQ := inf_centralizer_le_of_generalizedFitting_eq H.fstar
  rw [eq_bot_iff]
  intro n hn
  have hnC : n ∈ M ⊓ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) := by
    refine ⟨hNM hn, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h1 : n * q * n⁻¹ * q⁻¹ ∈ N := by
      rw [show n * q * n⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) by group]
      exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hMN (hQM hq)) n⁻¹).mp (N.inv_mem hn))
    have h2 : n * q * n⁻¹ * q⁻¹ ∈ inSubgroup (pCore 2) M :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hMQ (hNM hn)) q).mp hq)
        (Subgroup.inv_mem _ hq)
    have h3 : n * q * n⁻¹ * q⁻¹ ∈ N ⊓ inSubgroup (pCore 2) M := ⟨h1, h2⟩
    rw [hNQ, Subgroup.mem_bot] at h3
    calc q * n = (n * q * n⁻¹ * q⁻¹)⁻¹ * (n * q) := by group
      _ = n * q := by rw [h3, inv_one, one_mul]
  have h4 : n ∈ N ⊓ inSubgroup (pCore 2) M := ⟨hn, hCQ hnC⟩
  rwa [hNQ] at h4

theorem stronglyClosed_of_weaklyClosed (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput)
    (hwc : ∀ g : G, conjSubgroup g (PartTwo.omegaOneSub U) ≤ M →
      conjSubgroup g (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U) :
    ∀ u ∈ U, ∀ g : G, g * u * g⁻¹ ∈ M → g * u * g⁻¹ ∈ U := by
  have hroot := H.root hCen hU
  have hV : ∀ v ∈ PartTwo.omegaOneSub U, v ≠ 1 → ∀ g : G, g * v * g⁻¹ ∈ M →
      conjSubgroup g (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U := by
    intro v hv hv1 g hg
    have hgv : g * v * g⁻¹ ∈ conjSubgroup g (PartTwo.omegaOneSub U) := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
      exact hv
    have hgv1 : g * v * g⁻¹ ≠ 1 := fun h => hv1 (by
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    have hcomm := commute_of_isRootTypeTI hroot (g := g) (h := 1) (fun hbot => hgv1 (by
      have : g * v * g⁻¹ ∈ conjSubgroup g (PartTwo.omegaOneSub U) ⊓
          Subgroup.normalizer (conjSubgroup 1 (PartTwo.omegaOneSub U) : Set G) := by
        refine ⟨hgv, ?_⟩
        rw [conjSubgroup_one, H.normalizer_omega_eq]
        exact hg
      rwa [hbot, Subgroup.mem_bot] at this))
    refine hwc g fun z hz => ?_
    rw [← H.normalizer_omega_eq]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun c hc =>
      (hcomm z hz c (by rw [conjSubgroup_one]; exact hc)).symm)
  intro u hu g hg
  by_cases hu2 : u * u = 1
  · by_cases hu1 : u = 1
    · rw [hu1, mul_one, mul_inv_cancel]
      exact U.one_mem
    · have huV : u ∈ PartTwo.omegaOneSub U := (mem_omegaOneSub_iff H.comm).mpr ⟨hu, hu2⟩
      have hgV := hV u huV hu1 g hg
      have : g * u * g⁻¹ ∈ conjSubgroup g (PartTwo.omegaOneSub U) := by
        rw [mem_conjSubgroup, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
        exact huV
      rw [hgV] at this
      exact PartTwo.omegaOneSub_le U this
  · have hu2V : u * u ∈ PartTwo.omegaOneSub U :=
      (mem_omegaOneSub_iff H.comm).mpr ⟨U.mul_mem hu hu, by
        calc u * u * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = 1 := H.exp u hu⟩
    have hg2 : g * (u * u) * g⁻¹ ∈ M := by
      rw [show g * (u * u) * g⁻¹ = (g * u * g⁻¹) * (g * u * g⁻¹) by group]
      exact M.mul_mem hg hg
    have hgV := hV _ hu2V hu2 g hg2
    have hgM : g ∈ M := by
      rw [← H.normalizer_omega_eq]
      exact conjSubgroup_eq_self_iff.mp hgV
    exact (Subgroup.mem_normalizer_iff.mp (H.normal hgM) u).mp hu

theorem exists_sylow_le (hsc : ∀ u ∈ U, ∀ g : G, g * u * g⁻¹ ∈ M → g * u * g⁻¹ ∈ U) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ U ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  set S₀ := (P₀ : Subgroup ↥M).map M.subtype with hS₀
  have hS₀M : S₀ ≤ M := Subgroup.map_subtype_le _
  have hS₀2 : IsPGroup 2 S₀ := P₀.isPGroup'.map M.subtype
  have hUS₀ : U ≤ S₀ := by
    have hn : (U.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer H.le).mpr H.normal
    have hp : IsPGroup 2 (U.subgroupOf M) := H.two.comap_of_injective _ Subtype.val_injective
    have hle := IsPGroup.le_sylow_of_normal hp P₀
    intro u hu
    exact ⟨⟨u, H.le hu⟩, hle (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  obtain ⟨Q, hQ⟩ := hS₀2.exists_le_sylow
  have hQM : (Q : Subgroup G) ⊓ M ≤ S₀ := by
    have h2 : IsPGroup 2 (((Q : Subgroup G) ⊓ M).subgroupOf M) :=
      Q.isPGroup'.to_inf_left.comap_of_injective _ Subtype.val_injective
    have h1 : (P₀ : Subgroup ↥M) ≤ ((Q : Subgroup G) ⊓ M).subgroupOf M := fun z hz =>
      Subgroup.mem_subgroupOf.mpr ⟨hQ ⟨z, hz, rfl⟩, z.2⟩
    have h3 := P₀.is_maximal' h2 h1
    intro z hz
    have hz' : (⟨z, hz.2⟩ : ↥M) ∈ ((Q : Subgroup G) ⊓ M).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hz
    rw [h3] at hz'
    exact ⟨⟨z, hz.2⟩, hz', rfl⟩
  have hN : ∀ q ∈ (Q : Subgroup G), q ∈ Subgroup.normalizer (S₀ : Set G) → q ∈ S₀ := by
    intro q hq hqN
    have hqU : q ∈ Subgroup.normalizer (U : Set G) := by
      rw [← conjSubgroup_eq_self_iff]
      refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by rw [card_conjSubgroup])
      rw [mem_conjSubgroup] at hz
      have h2 : q * (q⁻¹ * z * q) * q⁻¹ ∈ S₀ :=
        (Subgroup.mem_normalizer_iff.mp hqN _).mp (hUS₀ hz)
      have h3 := hsc _ hz q (hS₀M h2)
      rwa [show q * (q⁻¹ * z * q) * q⁻¹ = z by group] at h3
    have hqM : q ∈ M := by
      rw [← H.normalizer_U_eq]
      exact hqU
    exact hQM ⟨hq, hqM⟩
  have : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  have hself : Subgroup.normalizer ((S₀.subgroupOf Q : Subgroup Q) : Set Q) = S₀.subgroupOf Q := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQ]
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hN x x.2 hx, fun hx => S₀.le_normalizer hx⟩
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.1
    Group.normalizerCondition_of_isNilpotent _ hself
  exact ⟨Q, le_trans (Subgroup.subgroupOf_eq_top.1 htop) hS₀M, le_trans hUS₀ hQ⟩

theorem not_weaklyClosed (hGold : GoldschmidtInput) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (o2 : pCore 2 G = ⊥)
    (hwc : ∀ g : G, conjSubgroup g (PartTwo.omegaOneSub U) ≤ M →
      conjSubgroup g (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U) : False := by
  classical
  have hsc := H.stronglyClosed_of_weaklyClosed hCen hU hwc
  obtain ⟨S, hSM, hUS⟩ := H.exists_sylow_le hsc
  have hUab : IsMulCommutative U := ⟨⟨fun a b => Subtype.ext (H.comm _ a.2 _ b.2)⟩⟩
  have hclosed : ∀ a ∈ U, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ U := by
    intro a ha g hg
    have := hsc a ha g⁻¹ (by rw [inv_inv]; exact hSM hg)
    rwa [inv_inv] at this
  obtain ⟨-, hb, -⟩ := hGold G S U hUS hUab hclosed
  set Mn := Subgroup.normalClosure (U : Set G) with hMn
  set Oc := CFSG.Open.goldschmidtOddCore ↥Mn with hOc
  have hUMn : U ≤ Mn := Subgroup.le_normalClosure
  have hUnot : ∀ g : G, conjSubgroup g U = U → g ∈ M := fun g hg => by
    rw [← H.normalizer_U_eq]
    exact conjSubgroup_eq_self_iff.mp hg
  have hU1 : U ≠ ⊥ := fun h => H.omega_ne_bot (by
    rw [eq_bot_iff, ← h]
    exact PartTwo.omegaOneSub_le U)
  have hnotall : ¬ ∀ g : G, g ∈ M := by
    intro hall
    have hUn : U.Normal := ⟨fun u hu g => by
      have := (Subgroup.mem_normalizer_iff.mp (H.normal (hall g)) u).mp hu
      exact this⟩
    have : U ≤ pCore 2 G := le_sSup ⟨hUn, H.two⟩
    rw [o2] at this
    exact hU1 (le_bot_iff.mp this)
  have hCM : ∀ u ∈ U, u ≠ 1 → ∀ x : G, u * x = x * u → x ∈ M := by
    intro u hu hu1 x hxu
    rw [← H.normalizer_U_eq]
    exact Tim77.mem_normalizer_of_commute_of_isTI H.ti hu hu1 hxu.symm
  have hOc : Oc = ⊥ := by
    have hchar : Oc.Characteristic :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_characteristic (G := ↥Mn)
    have hodd : Odd (Nat.card Oc) :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := ↥Mn)
    set OG := Oc.map Mn.subtype with hOG
    have hOGn : OG.Normal := ConjAct.normal_of_characteristic_of_normal
    have hOGodd : Odd (Nat.card OG) := by
      rw [hOG, Subgroup.card_map_of_injective Mn.subtype_injective]
      exact hodd
    have hOM : OG ⊓ M = ⊥ := by
      refine H.eq_bot_of_odd inf_le_right (fun m hm => mem_normalizer_inf
        ((Subgroup.normalizer_eq_top_iff.mpr hOGn) ▸ Subgroup.mem_top m)
          (Subgroup.le_normalizer hm))
        (Odd.of_dvd_nat hOGodd (Subgroup.card_dvd_of_le inf_le_left))
    have hfix : ∀ c ∈ U, c ≠ 1 → ∀ x ∈ OG, c * x = x * c → x = 1 := by
      intro c hc hc1 x hx hcx
      have : x ∈ OG ⊓ M := ⟨hx, hCM c hc hc1 x hcx⟩
      rwa [hOM, Subgroup.mem_bot] at this
    obtain ⟨a, ha, b, hb', ha1, hb1, hab⟩ := exists_ne_ne_of_four_le H.card4
    have haa : a * a = 1 := ((mem_omegaOneSub_iff H.comm).mp ha).2
    have hbb : b * b = 1 := ((mem_omegaOneSub_iff H.comm).mp hb').2
    have haU := PartTwo.omegaOneSub_le U ha
    have hbU := PartTwo.omegaOneSub_le U hb'
    have hab1 : a * b ≠ 1 := fun h => hab (by
      calc a = a * (b * b) := by rw [hbb, mul_one]
        _ = (a * b) * b := by group
        _ = b := by rw [h, one_mul])
    have hnorm : ∀ c : G, c ∈ Subgroup.normalizer (OG : Set G) := fun c =>
      (Subgroup.normalizer_eq_top_iff.mpr hOGn) ▸ Subgroup.mem_top c
    have hOG1 := eq_bot_of_fpf_klein haa hbb (hnorm a) (hnorm b) (hfix a haU ha1)
      (hfix b hbU hb1) (hfix (a * b) (U.mul_mem haU hbU) hab1)
    rw [hOG] at hOG1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Mn.subtype_injective).mp hOG1
  have hπinj : Function.Injective (QuotientGroup.mk' Oc) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOc]
  have hkey : ∀ L : Subgroup ↥Mn, L.Normal → IsPGroup 2 L → L.map Mn.subtype ≤ U := by
    intro L hLn hL2
    have hLle : L.map (QuotientGroup.mk' Oc) ≤ CFSG.Open.pCore 2 (↥Mn ⧸ Oc) := by
      rw [CFSG.pCore_eq_iSup]
      exact le_iSup_of_le (L.map (QuotientGroup.mk' Oc)) (le_iSup_of_le
        (hLn.map _ (QuotientGroup.mk'_surjective Oc)) (le_iSup_of_le (hL2.map _) le_rfl))
    rintro _ ⟨l, hl, rfl⟩
    have h1 : QuotientGroup.mk' Oc l ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc) := by
      rw [hb]
      exact Subgroup.mem_sup_left (hLle ⟨l, hl, rfl⟩)
    obtain ⟨u, hu, hul⟩ := h1
    rw [← hπinj hul]
    exact Subgroup.mem_subgroupOf.mp hu
  have hP : CFSG.Open.pCore 2 (↥Mn ⧸ Oc) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hNn => iSup_le fun hN2 => ?_
    set L := N.comap (QuotientGroup.mk' Oc) with hL
    have hLn : L.Normal := hNn.comap _
    have hL2 : IsPGroup 2 L := hN2.comap_of_injective _ hπinj
    set L₀ := L.map Mn.subtype with hL₀
    have hL₀U : L₀ ≤ U := hkey L hLn hL2
    have hL₀bot : L₀ = ⊥ := by
      by_contra hne
      apply hnotall
      intro g
      refine hUnot g (conjSubgroup_eq_of_isTI H.ti fun hbot => hne ?_)
      have hgL : conjSubgroup g L₀ ≤ U := by
        have hgMn : conjSubgroup g L₀ ≤ Mn := by
          intro z hz
          rw [mem_conjSubgroup] at hz
          rw [show z = g * (g⁻¹ * z * g) * g⁻¹ by group]
          exact (Subgroup.normalClosure_normal).conj_mem _ (hUMn (hL₀U hz)) g
        have hnorm : ((conjSubgroup g L₀).subgroupOf Mn).Normal := by
          refine ⟨fun n hn m => ?_⟩
          rw [Subgroup.mem_subgroupOf, mem_conjSubgroup] at hn ⊢
          obtain ⟨l, hl, hln⟩ := hn
          have hm' : g⁻¹ * (m : G) * g ∈ Mn :=
            by simpa using (Subgroup.normalClosure_normal).conj_mem _ m.2 g⁻¹
          have hLm := hLn.conj_mem l hl ⟨_, hm'⟩
          refine ⟨_, hLm, ?_⟩
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at hln ⊢
          rw [hln]
          group
        have h2 : IsPGroup 2 ((conjSubgroup g L₀).subgroupOf Mn) :=
          ((hL2.map Mn.subtype).map (MulAut.conj g).toMonoidHom).comap_of_injective _
            Subtype.val_injective
        have := hkey _ hnorm h2
        intro z hz
        exact this ⟨⟨z, hgMn hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      rw [eq_bot_iff]
      intro z hz
      have hz' : g * z * g⁻¹ ∈ U ⊓ conjSubgroup g U := by
        refine Subgroup.mem_inf.mpr ⟨hgL ?_, ?_⟩
        · rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
          exact hz
        · rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
          exact hL₀U hz
      rw [hbot, Subgroup.mem_bot] at hz'
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [hz']; group
    have hL1 : L = ⊥ := by
      rw [hL₀] at hL₀bot
      exact (Subgroup.map_eq_bot_iff_of_injective _ Mn.subtype_injective).mp hL₀bot
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Oc) N]
    rw [← hL, hL1, Subgroup.map_bot]
  rw [hP, bot_sup_eq] at hb
  have hab : ∀ x ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc),
      ∀ y ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc), x * y = y * x := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (H.comm _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
  have hsq : ∀ x ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc), x ^ 2 = 1 := by
    intro x hx
    have hx' := hx
    rw [hb] at hx'
    induction hx' using Subgroup.closure_induction with
    | mem t ht => exact ht.2
    | one => exact one_pow 2
    | mul s t hs ht ihs iht =>
        have hs' : s ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc) := by rw [hb]; exact hs
        have ht' : t ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc) := by rw [hb]; exact ht
        rw [(Commute.mul_pow (hab s hs' t ht') 2), ihs hs', iht ht', one_mul]
    | inv s hs ihs =>
        have hs' : s ∈ (U.subgroupOf Mn).map (QuotientGroup.mk' Oc) := by rw [hb]; exact hs
        rw [inv_pow, ihs hs', inv_one]
  apply H.ne
  refine le_antisymm (PartTwo.omegaOneSub_le U) fun u hu => ?_
  have h1 := hsq _ ⟨⟨u, hUMn hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [← map_pow] at h1
  have h2 : (⟨u, hUMn hu⟩ : ↥Mn) ^ 2 = 1 := hπinj (by rw [h1, map_one])
  refine (mem_omegaOneSub_iff H.comm).mpr ⟨hu, ?_⟩
  have := congrArg Subtype.val h2
  rw [Subgroup.coe_pow, sq] at this
  exact this

end S3Hyp

end CFSG.RankThree.GF2n.Tim78
