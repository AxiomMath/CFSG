module

public import CFSG.RankThree.GF2n.Parrott.Section3FusionGroup
public import CFSG.RankThree.GF2n.Parrott.Section3FusionLocal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GH74.PartII CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.OddStandard.ThmC
open CFSG.GH74.GLS.Bg.TwoGroups hiding IsElemAbelian

private def zOne : UT3 F4c := ⟨0, 0, 1⟩

private def zOmega : UT3 F4c := ⟨0, 0, ⟨0, 1⟩⟩

private def eOne : UT3 F4c := ⟨1, 0, 0⟩

private theorem zOne_facts : zOne.a = 0 ∧ zOne.b = 0 ∧ zOne ≠ 1 := by decide +kernel

private theorem zOmega_facts : zOmega.a = 0 ∧ zOmega.b = 0 ∧ zOmega ≠ 1 := by decide +kernel

private theorem zOneOmega_facts :
    (zOne * zOmega).a = 0 ∧ (zOne * zOmega).b = 0 ∧ zOne * zOmega ≠ 1 := by
  decide +kernel

private theorem eOne_facts : eOne.b = 0 ∧ eOne.a ≠ 0 := by decide +kernel

private theorem b_eq_zero_or_a_eq_zero {u : UT3 F4c} (h : u * u = 1) : u.b = 0 ∨ u.a = 0 :=
  ((T.sq_eq_one_iff_mem u).1 h).imp T.mem_A.1 T.mem_B.1

private theorem a_eq_zero_of_commute {u v : UT3 F4c} (hua : u.a = 0) (hub : u.b ≠ 0)
    (h : v * u = u * v) : v.a = 0 := by
  have hZ : u ∉ Subgroup.center (UT3 F4c) := fun hu => hub ((T.mem_center_iff u).1 hu).2
  have hv : v ∈ Subgroup.centralizer ({u} : Set (UT3 F4c)) :=
    Subgroup.mem_centralizer_singleton_iff.2 h
  rw [T.centralizer_of_mem_B (T.mem_B.2 hua) hZ] at hv
  exact T.mem_B.1 hv

private theorem commute_of_a_eq_zero {u v : UT3 F4c} (hu : u.a = 0) (hv : v.a = 0) :
    u * v = v * u :=
  (T.commute_iff u v).2 (by rw [hu, hv, zero_mul, zero_mul])

private theorem exists_conj_mem_of_mul_self {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    {t : X} (ht : t * t = 1) : ∃ g : X, g * t * g⁻¹ ∈ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht' : t ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact ht
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := by
    rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht', one_zpow]
  obtain ⟨R, hR⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact ⟨t, hR (Subgroup.mem_zpowers t), by simp [MulAut.conj_apply]⟩

theorem isConj_of_orderOf_eq_two_of_e16_alt5 {K : Type} [Group K] [Finite K] {B D : Subgroup K}
    (hDB : D ≤ B) (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥B →* alternatingGroup (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf B)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ B, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set K) ≤ B)
    (hodd : Odd B.index) (hproper : 1 < B.index) :
    ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hs, hk⟩ := hπ
  set S : Subgroup K := sylV π with hSdef
  have hSB : S ≤ B := sylV_le π
  have hS64 : Nat.card S = 64 := card_sylV hDB hD16 hs hk
  obtain ⟨e, he⟩ := exists_mulEquiv_sylV hDB hD hD16 hs hk hTrans
  set ι : UT3 F4c → K := fun u => ((e u : ↥S) : K) with hι
  have hιS : ∀ u, ι u ∈ S := fun u => (e u).2
  have hιB : ∀ u, ι u ∈ B := fun u => hSB (hιS u)
  have hιmul : ∀ u v, ι (u * v) = ι u * ι v := fun u v => by
    simp only [hι, map_mul, Subgroup.coe_mul]
  have hιone : ι 1 = 1 := by simp only [hι, map_one, Subgroup.coe_one]
  have hιinj : Function.Injective ι := fun u v h => e.injective (Subtype.ext h)
  have hιsurj : ∀ x ∈ S, ∃ u, ι u = x := fun x hx =>
    ⟨e.symm ⟨x, hx⟩, by simp only [hι, MulEquiv.apply_symm_apply]⟩
  have hιeq1 : ∀ u, ι u = 1 → u = 1 := fun u h => hιinj (h.trans hιone.symm)
  have hsqF : ∀ u : UT3 F4c, u.a = 0 → ι u * ι u = 1 := fun u hu => by
    rw [← hιmul, T.sq_eq_one_of_mem_B (T.mem_B.2 hu), hιone]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 6) (by rw [hS64]; norm_num)
  have hSidx : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index B
    have h2 := Subgroup.card_mul_index S
    rw [card_eq_960_of_e16_alt5 hs (card_ker_of_eq hDB hD16 hk)] at h1
    rw [hS64] at h2
    have := Nat.odd_iff.1 hodd
    omega
  have hCZ : ∀ z : UT3 F4c, z.a = 0 → z.b = 0 → z ≠ 1 →
      Subgroup.centralizer ({ι z} : Set K) = S := by
    intro z hza hzb hz1
    have hle : S ≤ Subgroup.centralizer ({ι z} : Set K) := by
      intro x hx
      obtain ⟨u, rfl⟩ := hιsurj x hx
      rw [Subgroup.mem_centralizer_singleton_iff, ← hιmul, ← hιmul,
        (T.mem_center_iff' z).2 ⟨hza, hzb⟩ u]
    refine (Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    rw [card_centralizer_eq_64 hDB hD16 hs hk hTrans hCent ((he z).2 hzb)
      (fun h => hz1 (hιeq1 z h)), hS64]
  have hmain : ∀ u : UT3 F4c, u.a = 0 → u.b ≠ 0 → ∃ d ∈ D, IsConj (ι u) d := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u₀, hu₀a, hu₀b, hu₀⟩ := hcon
    have H : ∀ v : UT3 F4c, v.a = 0 → v.b ≠ 0 → ∀ d ∈ D, ¬ IsConj (ι v) d := by
      intro v hva hvb d hd hc
      obtain ⟨g, -, hg⟩ := exists_conj_eq_of_sylV hDB hD hs hk e he hu₀a hu₀b hva hvb
      exact hu₀ d hd ((isConj_iff.2 ⟨g, hg⟩).trans hc)
    let F : Subgroup K := T.B.map (S.subtype.comp e.toMonoidHom)
    have hmemF : ∀ x, x ∈ F ↔ ∃ v : UT3 F4c, v.a = 0 ∧ ι v = x := fun x =>
      ⟨fun ⟨v, hv, hvx⟩ => ⟨v, T.mem_B.1 hv, hvx⟩,
        fun ⟨v, hv, hvx⟩ => ⟨v, T.mem_B.2 hv, hvx⟩⟩
    have hFS : F ≤ S := by
      intro x hx
      obtain ⟨v, -, rfl⟩ := (hmemF x).1 hx
      exact hιS v
    have hιF : ∀ v : UT3 F4c, v.a = 0 → ι v ∈ F := fun v hv => (hmemF _).2 ⟨v, hv, rfl⟩
    have hNF : ∀ g : K, (∀ f ∈ F, g * f * g⁻¹ ∈ F) → g ∈ B := by
      intro g hg
      obtain ⟨hza, hzb, hz1⟩ := zOne_facts
      obtain ⟨w, hwa, hw⟩ := (hmemF _).1 (hg _ (hιF zOne hza))
      have hwb : w.b = 0 := by
        by_contra hwb
        exact H w hwa hwb (ι zOne) ((he zOne).2 hzb)
          (by rw [hw]; exact (isConj_iff.2 ⟨g, rfl⟩).symm)
      have hw1 : w ≠ 1 := by
        rintro rfl
        rw [hιone] at hw
        apply hz1
        apply hιeq1
        calc ι zOne = g⁻¹ * (g * ι zOne * g⁻¹) * g := by group
          _ = 1 := by rw [← hw]; group
      have hgS : ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
        intro x hx
        have hxz : x * ι zOne = ι zOne * x := by
          rw [← hCZ zOne hza hzb hz1, Subgroup.mem_centralizer_singleton_iff] at hx
          exact hx
        rw [← hCZ w hwa hwb hw1, Subgroup.mem_centralizer_singleton_iff, hw]
        calc g * x * g⁻¹ * (g * ι zOne * g⁻¹) = g * (x * ι zOne) * g⁻¹ := by group
          _ = g * (ι zOne * x) * g⁻¹ := by rw [hxz]
          _ = g * ι zOne * g⁻¹ * (g * x * g⁻¹) := by group
      refine mem_of_conj_mem hD16 hTrans hCent fun d hd => ?_
      obtain ⟨v, rfl⟩ := hιsurj d (le_sylV hDB hk hd)
      obtain ⟨w', hw'⟩ := hιsurj _ (hgS _ (hιS v))
      have hvb : v.b = 0 := (he v).1 hd
      have hw'2 : w' * w' = 1 := by
        apply hιinj
        rw [hιmul, hw', hιone]
        have hv2 : ι v * ι v = 1 := by
          rw [← hιmul, T.sq_eq_one_of_mem_A (T.mem_A.2 hvb), hιone]
        calc g * ι v * g⁻¹ * (g * ι v * g⁻¹) = g * (ι v * ι v) * g⁻¹ := by group
          _ = 1 := by rw [hv2]; group
      rcases b_eq_zero_or_a_eq_zero hw'2 with hb | ha
      · rw [← hw']
        exact (he w').2 hb
      · by_contra hnot
        have hb : w'.b ≠ 0 := fun hb => hnot (by rw [← hw']; exact (he w').2 hb)
        exact H w' ha hb (ι v) hd (by rw [hw']; exact (isConj_iff.2 ⟨g, rfl⟩).symm)
    have hNC : ∀ v : UT3 F4c, v.a = 0 → v.b ≠ 0 → ∀ g : K, (∀ f ∈ F, g * f * g⁻¹ ∈ F) →
        g * ι v = ι v * g → g ∈ F := by
      intro v hva hvb g hg hc
      have hgS : g ∈ S :=
        mem_sylV_of_commute hk (hιS v) (fun h => hvb ((he v).1 h)) (hNF g hg) hc
      obtain ⟨w, rfl⟩ := hιsurj g hgS
      refine hιF w (a_eq_zero_of_commute hva hvb ?_)
      apply hιinj
      rw [hιmul, hιmul]
      exact hc
    have hCF : ∀ v : UT3 F4c, v.a = 0 → v.b ≠ 0 →
        Subgroup.centralizer ({ι v} : Set K) ≤ F := by
      intro v hva hvb
      set C := Subgroup.centralizer ({ι v} : Set K) with hCdef
      have hFC : F ≤ C := by
        intro x hx
        obtain ⟨w, hwa, rfl⟩ := (hmemF x).1 hx
        rw [Subgroup.mem_centralizer_singleton_iff, ← hιmul, ← hιmul,
          commute_of_a_eq_zero hwa hva]
      have hZC : ∀ z : UT3 F4c, z.a = 0 → ι z ∈ C := fun z hz => hFC (hιF z hz)
      let F' : Subgroup ↥C := F.subgroupOf C
      have hF'2 : IsPGroup 2 F' := by
        have hinj : Function.Injective (S.subtype.comp e.toMonoidHom) :=
          fun x y h => e.injective (S.subtype_injective h)
        have hcard : Nat.card F' = 16 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv,
            Subgroup.card_map_of_injective hinj]
          exact T.card_B
        exact IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
      have hF'ab : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := by
        intro x hx y hy
        obtain ⟨w, hwa, hw⟩ := (hmemF _).1 (Subgroup.mem_subgroupOf.1 hx)
        obtain ⟨w', hw'a, hw'⟩ := (hmemF _).1 (Subgroup.mem_subgroupOf.1 hy)
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hw, ← hw', ← hιmul, ← hιmul,
          commute_of_a_eq_zero hwa hw'a]
      have hF'N : ∀ g : ↥C, g ∈ Subgroup.normalizer (F' : Set ↥C) → g ∈ F' := by
        intro g hg
        rw [Subgroup.mem_subgroupOf]
        refine hNC v hva hvb (g : K) (fun f hf => ?_)
          (Subgroup.mem_centralizer_singleton_iff.1 g.2)
        have h1 := (Subgroup.mem_normalizer_iff.1 hg ⟨f, hFC hf⟩).1
          (Subgroup.mem_subgroupOf.2 hf)
        exact Subgroup.mem_subgroupOf.1 h1
      have hcent : ∀ z : UT3 F4c, z.a = 0 → z.b = 0 → z ≠ 1 → ∀ hz : ι z ∈ C,
          IsPGroup 2 (Subgroup.centralizer ({(⟨ι z, hz⟩ : ↥C)} : Set ↥C)) := by
        intro z hza hzb hz1 hz
        have hle : Subgroup.centralizer ({(⟨ι z, hz⟩ : ↥C)} : Set ↥C) ≤ S.comap C.subtype := by
          intro y hy
          rw [Subgroup.mem_comap, Subgroup.coe_subtype, ← hCZ z hza hzb hz1,
            Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
        exact (hS2.comap_of_injective C.subtype C.subtype_injective).to_le hle
      obtain ⟨h1a, h1b, h11⟩ := zOne_facts
      obtain ⟨h2a, h2b, h21⟩ := zOmega_facts
      obtain ⟨h12a, h12b, h121⟩ := zOneOmega_facts
      let z₁ : ↥C := ⟨ι zOne, hZC zOne h1a⟩
      let z₂ : ↥C := ⟨ι zOmega, hZC zOmega h2a⟩
      have hz₁₂ : z₁ * z₂ = ⟨ι (zOne * zOmega), hZC _ h12a⟩ := Subtype.ext (hιmul _ _).symm
      have hGL := eq_top_of_normalizer_le_of_isPGroup_centralizer hF'2 hF'ab hF'N
        (z₁ := z₁) (z₂ := z₂) (Subtype.ext (hsqF zOne h1a)) (Subtype.ext (hsqF zOmega h2a))
        (hcent zOne h1a h1b h11 _) (hcent zOmega h2a h2b h21 _)
        (by rw [hz₁₂]; exact hcent _ h12a h12b h121 _)
      intro x hx
      have hxF : (⟨x, hx⟩ : ↥C) ∈ F' := by
        rw [hGL]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hxF
    have hCB : ∀ w ∈ S, w * w = 1 → w ≠ 1 → Subgroup.centralizer ({w} : Set K) ≤ B := by
      intro w hw hw2 hw1
      obtain ⟨u, rfl⟩ := hιsurj w hw
      by_cases hb : u.b = 0
      · exact hCent _ ((he u).2 hb) hw1
      · have hu2 : u * u = 1 := hιinj (by rw [hιmul, hw2, hιone])
        have ha := (b_eq_zero_or_a_eq_zero hu2).resolve_left hb
        exact (hCF u ha hb).trans (hFS.trans hSB)
    obtain ⟨h1a, h1b, h11⟩ := zOne_facts
    have hz1D : ι zOne ∈ D := (he zOne).2 h1b
    have ht₀B : ∀ x : K, IsConj (ι u₀) x → x ∈ B := by
      intro x hx
      have hxz : ¬ IsConj x (ι zOne) := fun h => hu₀ _ hz1D (hx.trans h)
      have hx2 : x * x = 1 := by
        obtain ⟨c, rfl⟩ := isConj_iff.1 hx
        calc c * ι u₀ * c⁻¹ * (c * ι u₀ * c⁻¹) = c * (ι u₀ * ι u₀) * c⁻¹ := by group
          _ = 1 := by rw [hsqF u₀ hu₀a]; group
      obtain ⟨w, hw2, hw1, hxw, hzw⟩ := exists_commute_of_not_isConj hx2 (hsqF zOne h1a) hxz
      have hwS : w ∈ S := by
        rw [← hCZ zOne h1a h1b h11, Subgroup.mem_centralizer_singleton_iff]
        exact hzw.symm
      exact hCB w hwS hw2 hw1 (Subgroup.mem_centralizer_singleton_iff.2 hxw)
    obtain ⟨heb, hea⟩ := eOne_facts
    let L : Subgroup K := Subgroup.normalClosure ({ι u₀} : Set K)
    have hLn : L.Normal := Subgroup.normalClosure_normal
    have hLB : L ≤ B := by
      change Subgroup.closure (Group.conjugatesOfSet ({ι u₀} : Set K)) ≤ B
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ht₀B x hyx
    have ht₀L : ι u₀ ∈ L := Subgroup.subset_normalClosure (Set.mem_singleton _)
    have heD : ι eOne ∈ D := (he eOne).2 heb
    have hcD : ι eOne * ι u₀ * (ι eOne)⁻¹ * (ι u₀)⁻¹ ∈ D := by
      have h1 : ι u₀ * (ι eOne)⁻¹ * (ι u₀)⁻¹ ∈ D :=
        conj_mem_of_ker hDB hk (hιB u₀) (inv_mem heD)
      have := mul_mem heD h1
      simpa only [mul_assoc] using this
    have hcL : ι eOne * ι u₀ * (ι eOne)⁻¹ * (ι u₀)⁻¹ ∈ L :=
      mul_mem (hLn.conj_mem _ ht₀L _) (inv_mem ht₀L)
    have hc1 : ι eOne * ι u₀ * (ι eOne)⁻¹ * (ι u₀)⁻¹ ≠ 1 := by
      intro h
      apply hea
      refine a_eq_zero_of_commute hu₀a hu₀b ?_
      apply hιinj
      rw [hιmul, hιmul]
      calc ι eOne * ι u₀ = (ι eOne * ι u₀ * (ι eOne)⁻¹ * (ι u₀)⁻¹) * ι u₀ * ι eOne := by group
        _ = ι u₀ * ι eOne := by rw [h]; group
    have hDL : D ≤ L := by
      intro d hd
      by_cases hd1 : d = 1
      · rw [hd1]
        exact one_mem _
      obtain ⟨g, -, hgd⟩ := hTrans _ hcD d hd hc1 hd1
      rw [← hgd]
      exact hLn.conj_mem _ hcL g
    have hBtop := eq_top_of_normal_of_le hDB hD hD16 hs hk hTrans hCent hLn hLB hDL ht₀L
      (fun h => hu₀b ((he u₀).1 h))
    rw [hBtop, Subgroup.index_top] at hproper
    exact lt_irrefl _ hproper
  obtain ⟨h1a, h1b, h11⟩ := zOne_facts
  have hz1D : ι zOne ∈ D := (he zOne).2 h1b
  have hz11 : ι zOne ≠ 1 := fun h => h11 (hιeq1 _ h)
  have hD1 : ∀ d ∈ D, d ≠ 1 → IsConj d (ι zOne) := fun d hd hd1 => by
    obtain ⟨g, -, hg⟩ := hTrans d hd _ hz1D hd1 hz11
    exact isConj_iff.2 ⟨g, hg⟩
  have hall : ∀ x : K, orderOf x = 2 → IsConj x (ι zOne) := by
    intro x hx
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      norm_num at hx
    obtain ⟨g, hg⟩ := exists_conj_mem_of_mul_self (hS2.toSylow hSidx) hx2
    rw [IsPGroup.toSylow_coe hS2 hSidx] at hg
    obtain ⟨u, hu⟩ := hιsurj _ hg
    have hxu : IsConj x (ι u) := by
      rw [hu]
      exact isConj_iff.2 ⟨g, rfl⟩
    have hu1 : ι u ≠ 1 := by
      rw [hu]
      intro h
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    by_cases hb : u.b = 0
    · exact hxu.trans (hD1 _ ((he u).2 hb) hu1)
    · have hu2 : u * u = 1 := by
        apply hιinj
        rw [hιmul, hu, hιone]
        calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
          _ = 1 := by rw [hx2]; group
      have ha := (b_eq_zero_or_a_eq_zero hu2).resolve_left hb
      obtain ⟨d, hd, hud⟩ := hmain u ha hb
      have hd1 : d ≠ 1 := by
        rintro rfl
        exact hu1 (isConj_one_left.1 hud)
      exact hxu.trans (hud.trans (hD1 d hd hd1))
  intro x y hx hy
  exact (hall x hx).trans (hall y hy).symm

end CFSG.RankThree.GF2n.Parrott
