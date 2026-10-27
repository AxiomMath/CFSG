module

public import CFSG.Quasithin.Recognition.RuTypeJ29d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem exists_S1_B7
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hxL : x ∈ M.L)
    (hxLs : x ∈ Ls s) : ∃ b ∈ M.S1, ∃ k : ℕ, x = b * (M.cel : G) ^ k := by
  have hxC := Ls_le_Cen s hxLs
  obtain ⟨k, hk⟩ := M.θ_mem_of_comm hs hs1 (l := ⟨x, hxL⟩) (mem_Cen.mp hxC)
  have hcC : (M.cel : G) ∈ Cen s := mem_Cen.mpr (M.mem_S0.mp hs).2
  have hker : (⟨x, hxL⟩ * M.cel⁻¹ ^ k.val : M.L) ∈ M.θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv, hk, M.θ_cel, inv_pow, mul_inv_cancel]
  rw [M.θ_ker, Subgroup.mem_subgroupOf] at hker
  have hS : x * ((M.cel : G)⁻¹) ^ k.val ∈ ruS M.L := by simpa using hker
  have hS3 : x * ((M.cel : G)⁻¹) ^ k.val ∈ M.S3 := by
    rw [← M.centralizer_eq_S3 hs hs1]
    exact ⟨hS, mul_mem hxC (pow_mem (inv_mem hcC) _)⟩
  have hLs : x * ((M.cel : G)⁻¹) ^ k.val ∈ Ls s := by
    refine mul_mem hxLs (pow_mem (inv_mem (mem_Ls_of_odd hcC ?_)) _)
    have := M.odd_orderOf_cel_pow 1
    simpa using this
  refine ⟨_, M.mem_S1_of_mem_Ls hs hs1 hS3 hLs, k.val, ?_⟩
  rw [inv_pow, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_conj_seven {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {Y : Subgroup G}
    (hY : Y ≤ M.L ⊓ Cen s) (hY7 : Nat.card Y = 7) :
    ∃ g ∈ M.L ⊓ Cen s, Y = M.B7.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set CL := M.L ⊓ Cen s
  have hcard : Nat.card CL = 2 ^ 8 * 7 := M.card_centralizer_L hs hs1
  have hfac : (Nat.card CL).factorization 7 = 1 := by
    rw [hcard, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 2 by norm_num),
      Nat.Prime.factorization_self (show Nat.Prime 7 by norm_num)]
  have hB7 : M.B7 ≤ CL := by
    rw [Subgroup.zpowers_le]
    exact ⟨M.cel.2, mem_Cen.mpr (M.mem_S0.mp hs).2⟩
  have hc1 : Nat.card (Y.subgroupOf CL) = 7 ^ (Nat.card CL).factorization 7 := by
    rw [card_subgroupOf_of_le hY, hY7, hfac, pow_one]
  have hc2 : Nat.card (M.B7.subgroupOf CL) = 7 ^ (Nat.card CL).factorization 7 := by
    rw [card_subgroupOf_of_le hB7, M.card_B7, hfac, pow_one]
  let P1 : Sylow 7 CL := Sylow.ofCard _ hc1
  let P2 : Sylow 7 CL := Sylow.ofCard _ hc2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CL P2 P1
  refine ⟨g, g.2, le_antisymm ?_ ?_⟩
  · intro y hy
    have hy1 : (⟨y, hY hy⟩ : CL) ∈ (P1 : Subgroup CL) := Subgroup.mem_subgroupOf.mpr hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy1
    have h2 := Subgroup.mem_subgroupOf.mp hy1
    refine ⟨_, h2, ?_⟩
    simp [MulAut.conj_apply]
    group
  · rintro _ ⟨b, hb, rfl⟩
    have hb1 : (⟨b, hB7 hb⟩ : CL) ∈ (P2 : Subgroup CL) := Subgroup.mem_subgroupOf.mpr hb
    have hb2 : g * ⟨b, hB7 hb⟩ * g⁻¹ ∈ (P1 : Subgroup CL) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hb1, by simp [MulAut.conj_apply]⟩
    have := Subgroup.mem_subgroupOf.mp hb2
    simpa using this

instance involutionCore_normal (s : G) : (CFSG.BenderSuzuki.involutionCore (Ls s)).Normal where
  conj_mem x hx g := by
    have h := conj_mem_L0G (Ls_le_Cen s g.2) ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h
    have : y = g * x * g⁻¹ := Subtype.ext (by simpa using hyx)
    rw [← this]
    exact hy

theorem Ls_eq_L0G_and_sz
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Ls s = L0G s ∧ Nonempty (CFSG.BenderSuzuki.involutionCore (Ls s) ≃* CFSG.Open.Sz 1) ∧
      Nat.card (Ls s) = 29120 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, i, e, hBT⟩ := M.exists_benderType_L0 hs hs1
  set X := Ls s
  set L0 := CFSG.BenderSuzuki.involutionCore X
  have hsuz : i = 2 → ∃ a, n = 2 * a + 1 ∧
      Nonempty (L0 ≃* CFSG.Theory.Comparator.SzModel a) := by
    intro hi
    cases hBT with
    | linear n hn e => omega
    | suzuki a ha e => exact ⟨a, rfl, ⟨e⟩⟩
    | unitary n hn e => omega
  have hVLs : ∀ v ∈ ruV M.L, v ∈ Ls s := fun v hv => M.S1_le_Ls hs hs1 (M.V_le_S1 hv)
  have hVL0 : ∀ v (hv : v ∈ ruV M.L), (⟨v, hVLs v hv⟩ : X) ∈ L0 := by
    intro v hv
    by_cases hv1 : v = 1
    · subst hv1
      exact one_mem _
    · exact mem_involutionCore _ hv1 (M.sq_eq_one_of_V hv)
  set V0 : Subgroup L0 := ((ruV M.L).subgroupOf X).subgroupOf L0 with hV0
  have hV0card : Nat.card V0 = 8 := by
    rw [← M.toRuData.card_V]
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : L0) : X), Subgroup.mem_subgroupOf.mp
          (Subgroup.mem_subgroupOf.mp x.2)⟩
        invFun := fun v => ⟨⟨⟨v, hVLs v v.2⟩, hVL0 v v.2⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr v.2)⟩
        left_inv := fun x => rfl
        right_inv := fun v => rfl }
  have hV0p : IsPGroup 2 V0 := IsPGroup.of_card (n := 3) (by rw [hV0card]; norm_num)
  obtain ⟨Q, hQ⟩ := hV0p.exists_le_sylow
  obtain ⟨t, hc⟩ := hBT.exists_benderCore Q
  have hι : ∀ x : L0, ((x : X) : G) ∈ Ls s := fun x => (x : X).2
  set z0 : L0 := ⟨⟨M.z, hVLs _ M.z_mem_V⟩, hVL0 _ M.z_mem_V⟩
  have hz0Q : z0 ∈ Q := hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr M.z_mem_V))
  have hinvR : ∀ v (hv : v ∈ ruV M.L), v ≠ 1 →
      (⟨⟨v, hVLs v hv⟩, hVL0 v hv⟩ : L0) ∈ rootCenter (Q : Subgroup L0) := by
    intro v hv hv1
    refine hc.center_of_involution _ (le_borel _ (hQ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mpr hv)))) ?_
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext; apply Subtype.ext
      simpa using M.sq_eq_one_of_V hv
    · intro h
      exact hv1 (congrArg (fun x : L0 => ((x : X) : G)) h)
  have hz0R : z0 ∈ rootCenter (Q : Subgroup L0) := hinvR _ M.z_mem_V M.z_ne_one
  have hQS1 : ∀ x ∈ (Q : Subgroup L0), ((x : X) : G) ∈ M.S1 := by
    intro x hx
    have hcomm : x * z0 = z0 * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz0R).2 x hx
    have h := congrArg (fun y : L0 => ((y : X) : G)) hcomm
    simp only [Subgroup.coe_mul] at h
    exact M.mem_S1_of_comm_V hs hs1 M.z_mem_V M.z_ne_one (hι x) h
  have hRV : ∀ x ∈ rootCenter (Q : Subgroup L0), ((x : X) : G) ∈ ruV M.L := by
    intro x hx
    refine M.mem_V_of_S1_sq (hQS1 x (Subgroup.mem_inf.mp hx).1) ?_
    have h := hc.center_sq x hx
    have h' := congrArg (fun y : L0 => ((y : X) : G)) h
    simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h'
    rw [pow_two]
    exact h'
  have hRcard : Nat.card (rootCenter (Q : Subgroup L0)) = 8 := by
    apply le_antisymm
    · rw [← hV0card]
      refine Subgroup.card_le_of_le fun x hx => ?_
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hRV x hx))
    · rw [← hV0card]
      refine Subgroup.card_le_of_le fun x hx => ?_
      have hv : ((x : X) : G) ∈ ruV M.L :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
      by_cases hx1 : ((x : X) : G) = 1
      · have : x = 1 := Subtype.ext (Subtype.ext hx1)
        rw [this]
        exact one_mem _
      · have := hinvR _ hv hx1
        exact this
  have hn : n = 3 := by
    have h := hc.card_center
    rw [hRcard] at h
    have : (2 : ℕ) ^ n = 2 ^ 3 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hn
  have hQcard : Nat.card (Q : Subgroup L0) = 8 ^ i := by rw [hc.card_eq]; norm_num
  have hQ64 : Nat.card (Q : Subgroup L0) ≤ 64 := by
    have h64 : Nat.card M.S1 = 64 := by rw [M.card_S1]; norm_num
    rw [← h64]
    let f : ↥(Q : Subgroup L0) → M.S1 := fun x => ⟨((x : L0) : X), hQS1 x x.2⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      have := congrArg Subtype.val h
      simpa [f] using this
    exact Nat.card_le_card_of_injective f hf
  have hi2 : i ≤ 2 := by
    by_contra h
    push Not at h
    have : 8 ^ 3 ≤ 8 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [← hQcard] at this
    omega
  have hcelL0 : (M.cel : G) ∈ L0G s := by
    have he : e = 1 := by
      rcases hBT.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi3, -, -⟩
      · exact he
      · exact he
      · omega
    subst he
    set C := cartan (Q : Subgroup L0) t
    have hCcard : Nat.card C = 7 := by rw [hc.card_cartan]; norm_num
    have hinvC : ∀ x ∈ C, t * x * t = x⁻¹ := by
      have hsub : {x : L0 | x ∈ C ∧ t * x * t = x⁻¹} ⊆ (C : Set L0) := fun x hx => hx.1
      have hle : (C : Set L0).ncard ≤ {x : L0 | x ∈ C ∧ t * x * t = x⁻¹}.ncard := by
        have h1 : (C : Set L0).ncard = 7 := by
          rw [← Nat.card_coe_set_eq]
          exact hCcard
        rw [h1, hc.ncard_inv]
        norm_num
      have heq := Set.eq_of_subset_of_ncard_le hsub hle
      intro x hx
      have : x ∈ {x : L0 | x ∈ C ∧ t * x * t = x⁻¹} := heq ▸ hx
      exact this.2
    set CG : Subgroup G := (C.map L0.subtype).map X.subtype with hCG
    have hCGcard : Nat.card CG = 7 := by
      rw [hCG, Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.card_map_of_injective L0.subtype_injective, hCcard]
    have hCGL : CG ≤ M.L ⊓ Cen s := by
      rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨?_, Ls_le_Cen s (hι x)⟩
      have hxN : x ∈ Subgroup.normalizer ((Q : Subgroup L0) : Set L0) :=
        (Subgroup.mem_inf.mp hx).1
      rw [M.one.eq_normalizer]
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      by_cases hv1 : v = 1
      · subst hv1; simp
      have hvQ : (⟨⟨v, hVLs v hv⟩, hVL0 v hv⟩ : L0) ∈ (Q : Subgroup L0) :=
        hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hv))
      have hconj := (Subgroup.mem_normalizer_iff.mp hxN _).mp hvQ
      have hS1 := hQS1 _ hconj
      refine M.mem_V_of_S1_sq hS1 ?_
      have hy2 : (⟨⟨v, hVLs v hv⟩, hVL0 v hv⟩ : L0) ^ 2 = 1 :=
        Subtype.ext (Subtype.ext (by simpa using M.sq_eq_one_of_V hv))
      have h2 : (x * ⟨⟨v, hVLs v hv⟩, hVL0 v hv⟩ * x⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hy2]; group
      have := congrArg (fun y : L0 => ((y : X) : G)) h2
      simpa using this
    obtain ⟨g, hg, hgC⟩ := M.exists_conj_seven hs hs1 hCGL hCGcard
    have hcelC : g * (M.cel : G) * g⁻¹ ∈ CG := by
      rw [hgC]
      exact ⟨_, Subgroup.mem_zpowers _, rfl⟩
    obtain ⟨y, ⟨x, hxC, rfl⟩, hxy⟩ := hcelC
    have htx := hinvC x hxC
    set tG : G := ((t : X) : G) with htG
    have htx' : tG * ((x : X) : G) * tG = ((x : X) : G)⁻¹ := by
      have := congrArg (fun y : L0 => ((y : X) : G)) htx
      simpa using this
    have hxcel : ((x : X) : G) = g * (M.cel : G) * g⁻¹ := hxy
    set t' : G := g⁻¹ * tG * g with ht'
    have ht'c : t' * (M.cel : G) * t' = (M.cel : G)⁻¹ := by
      rw [ht']
      have e2 : (M.cel : G) = g⁻¹ * ((x : X) : G) * g := by rw [hxcel]; group
      calc g⁻¹ * tG * g * (M.cel : G) * (g⁻¹ * tG * g) = g⁻¹ * (tG * ((x : X) : G) * tG) * g := by
            rw [e2]; group
        _ = (M.cel : G)⁻¹ := by rw [htx', e2]; group
    have ht2 : t * t = 1 := hc.sq_eq_one
    have htG2 : tG * tG = 1 := by
      have := congrArg (fun y : L0 => ((y : X) : G)) ht2
      simpa using this
    have hgCen : g ∈ Cen s := (Subgroup.mem_inf.mp hg).2
    have ht'L0 : t' ∈ L0G s := by
      have h := conj_mem_L0G (inv_mem hgCen) (show tG ∈ L0G s from ⟨t, t.2, rfl⟩)
      simpa [ht'] using h
    have hcC : (M.cel : G) ∈ Cen s := mem_Cen.mpr (M.mem_S0.mp hs).2
    have hcLs : (M.cel : G) ∈ Ls s := mem_Ls_of_odd hcC (by simpa using M.odd_orderOf_cel_pow 1)
    have ht'Ls : t' ∈ Ls s := L0G_le_Ls s ht'L0
    have ht'2 : t' * t' = 1 := by
      rw [ht']
      calc g⁻¹ * tG * g * (g⁻¹ * tG * g) = g⁻¹ * (tG * tG) * g := by group
        _ = 1 := by rw [htG2]; group
    have hprod : (t' * (M.cel : G)) ^ 2 = 1 := by
      rw [pow_two]
      calc t' * (M.cel : G) * (t' * (M.cel : G)) = (t' * (M.cel : G) * t') * M.cel := by group
        _ = 1 := by rw [ht'c]; group
    have hprod1 : t' * (M.cel : G) ≠ 1 := by
      intro h
      have hcel : (M.cel : G) = t' := by
        calc (M.cel : G) = t'⁻¹ * (t' * M.cel) := by group
          _ = t' := by rw [h, mul_one, inv_eq_of_mul_eq_one_right ht'2]
      have h7 := M.orderOf_cel
      have h2 : (M.cel : G) ^ 2 = 1 := by rw [hcel, pow_two, ht'2]
      have := orderOf_dvd_of_pow_eq_one h2
      rw [h7] at this
      norm_num at this
    have hpL0 : t' * (M.cel : G) ∈ L0G s :=
      mem_L0G_of_inv (mul_mem ht'Ls hcLs) hprod1 hprod
    have : (M.cel : G) = t'⁻¹ * (t' * M.cel) := by group
    rw [this]
    exact mul_mem (inv_mem ht'L0) hpL0
  have hpow : ∀ y : X, ∃ k : ℕ, ((y : G)) ^ 2 ^ k ∈ L0G s := by
    intro y
    let P : Sylow 2 L0 := Q
    have hF := Sylow.normalizer_sup_eq_top (N := L0) P
    have hy : y ∈ Subgroup.normalizer (((P : Subgroup L0).map L0.subtype : Subgroup X) : Set X) ⊔
        L0 := by rw [hF]; exact Subgroup.mem_top _
    obtain ⟨a, ha, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have haL : ((a : X) : G) ∈ M.L := by
      rw [M.one.eq_normalizer]
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      by_cases hv1 : v = 1
      · subst hv1; simp
      have hvQ : (⟨⟨v, hVLs v hv⟩, hVL0 v hv⟩ : L0) ∈ (Q : Subgroup L0) :=
        hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hv))
      have hvQX : (⟨v, hVLs v hv⟩ : X) ∈ (P : Subgroup L0).map L0.subtype := ⟨_, hvQ, rfl⟩
      have hconj := (Subgroup.mem_normalizer_iff.mp ha _).mp hvQX
      obtain ⟨w, hwQ, hw⟩ := hconj
      have hS1 := hQS1 _ hwQ
      have hw' : (((w : L0) : X) : G) = (a : G) * v * (a : G)⁻¹ := by
        have := congrArg Subtype.val hw
        simpa using this
      rw [hw'] at hS1
      refine M.mem_V_of_S1_sq hS1 ?_
      rw [conj_pow, M.sq_eq_one_of_V hv]
      group
    obtain ⟨b, hb, k, hk⟩ := M.exists_S1_B7 hs hs1 haL a.2
    refine ⟨6, ?_⟩
    have hcelk : (M.cel : G) ^ k ∈ L0G s := pow_mem hcelL0 k
    have hlG : ((l : X) : G) ∈ L0G s := ⟨l, hl, rfl⟩
    have hm : (M.cel : G) ^ k * l ∈ L0G s := mul_mem hcelk hlG
    have hNn : ((L0G s).subgroupOf (Cen s)).Normal :=
      ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (by
        simpa using conj_mem_L0G g.2 (Subgroup.mem_subgroupOf.mp hx))⟩
    have hbC : b ∈ Cen s := M.S3_le_Cen hs hs1 (M.S1_le_S3 hb)
    have hmC : (M.cel : G) ^ k * l ∈ Cen s := Ls_le_Cen s (L0G_le_Ls s hm)
    have hq : (QuotientGroup.mk (⟨((a * l : X) : G), Ls_le_Cen s (a * l).2⟩ : Cen s) :
        Cen s ⧸ (L0G s).subgroupOf (Cen s)) = QuotientGroup.mk (⟨b, hbC⟩ : Cen s) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (((⟨((a * l : X) : G), Ls_le_Cen s (a * l).2⟩ : Cen s)⁻¹ * ⟨b, hbC⟩ : Cen s) :
          G) = ((M.cel : G) ^ k * l)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hk]
        group
      rw [e]
      exact inv_mem hm
    have hb64 : b ^ 2 ^ 6 = 1 := by
      have := pow_card_eq_one' (G := M.S1) (x := ⟨b, hb⟩)
      rw [M.card_S1] at this
      simpa using congrArg Subtype.val this
    have hq' : (QuotientGroup.mk (⟨((a * l : X) : G), Ls_le_Cen s (a * l).2⟩ : Cen s) :
        Cen s ⧸ (L0G s).subgroupOf (Cen s)) ^ 2 ^ 6 = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨b, hbC⟩ : Cen s) ^ 2 ^ 6 = 1 := Subtype.ext (by simpa using hb64)
      rw [this, QuotientGroup.mk_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq'
    simpa using Subgroup.mem_subgroupOf.mp hq'
  have hNn : ((L0G s).subgroupOf (Cen s)).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (by
      simpa using conj_mem_L0G g.2 (Subgroup.mem_subgroupOf.mp hx))⟩
  have hQ2 : IsPGroup 2 (Cen s ⧸ (L0G s).subgroupOf (Cen s)) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hLsq := CFSG.GorensteinWalter.isPGroup_quotient_pResidualOf (Cen s) 2 Nat.prime_two
    obtain ⟨a, ha⟩ := hLsq (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at ha
    have hyLs : ((y : G)) ^ 2 ^ a ∈ Ls s := by simpa using Subgroup.mem_subgroupOf.mp ha
    obtain ⟨b, hb⟩ := hpow ⟨_, hyLs⟩
    refine ⟨a + b, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simp only [SubgroupClass.coe_pow]
    rw [pow_add, pow_mul]
    exact hb
  have hLsle : Ls s ≤ L0G s :=
    CFSG.GorensteinWalter.pResidualOf_le_of_quotient_isPGroup (Cen s) (L0G s) 2 Nat.prime_two
      ((L0G_le_Ls s).trans (Ls_le_Cen s)) hNn hQ2
  have hLsEq : Ls s = L0G s := le_antisymm hLsle (L0G_le_Ls s)
  refine ⟨hLsEq, ?_⟩
  have hcardLs : Nat.card (Ls s) = Nat.card L0 := by
    rw [hLsEq]
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hS1L0 : 2 ^ 6 ∣ Nat.card L0 := by
    have h1 : Nat.card (L0G s) = Nat.card L0 :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [← h1, ← hLsEq, ← M.card_S1]
    exact Subgroup.card_dvd_of_le (M.S1_le_Ls hs hs1)
  rcases hBT.cases' with ⟨hi1, he1, -⟩ | ⟨hi2', he1, a, ha, ha3⟩ | ⟨hi3, -, -⟩
  · exfalso
    subst hi1; subst he1
    have hcard := hBT.card_eq
    norm_num at hcard
    rw [hcard] at hS1L0
    norm_num at hS1L0
  · subst hi2'; subst he1
    have ha1 : a = 1 := by omega
    subst ha1
    have hcard := hBT.card_eq
    norm_num at hcard
    refine ⟨?_, by rw [hcardLs, hcard]⟩
    obtain ⟨a', ha', ⟨e'⟩⟩ := hsuz rfl
    have ha1' : a' = 1 := by omega
    subst ha1'
    exact ⟨e'.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz 1))⟩
  · omega

end RuDataM

end CFSG.Quasithin.RuType
