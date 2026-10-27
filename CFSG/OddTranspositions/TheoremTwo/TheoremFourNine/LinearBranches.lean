module

public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8PglLayer
public import CFSG.GH74.GLS.SP.Local.SPLTabL2
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.FiniteA5
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.Recognition
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.SylowSixteen

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem commutatorElement_mem_of_index_two {H : Subgroup G} (hH : H.index = 2) (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ H := by
  have h1 : x * y ∈ H ↔ (x ∈ H ↔ y ∈ H) := Subgroup.mul_mem_iff_of_index_two hH
  have h2 : x⁻¹ * y⁻¹ ∈ H ↔ (x⁻¹ ∈ H ↔ y⁻¹ ∈ H) := Subgroup.mul_mem_iff_of_index_two hH
  rw [H.inv_mem_iff, H.inv_mem_iff] at h2
  have := (Subgroup.mul_mem_iff_of_index_two hH (a := x * y) (b := x⁻¹ * y⁻¹)).mpr
    (by rw [h1, h2])
  simpa [mul_assoc] using this

theorem false_of_normal_pgl2 {L N₀ X : Subgroup G} (hab : Odd ((⁅L, L⁆).relIndex L))
    (hN₀L : N₀ ≤ L) (hN₀n : (N₀.subgroupOf L).Normal) (hodd : Odd (N₀.relIndex L))
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) (eN : N₀ ≃* PGL2 K)
    (hXL : X ≤ L) (hX : Nonempty (X ≃* alternatingGroup (Fin 5))) : False := by
  classical
  have hXN₀ := le_of_odd_relIndex_of_A5 hN₀L hN₀n hodd hXL hX
  obtain ⟨eX⟩ := hX
  have h60 : 60 ∣ Nat.card N₀ := by
    have := Subgroup.card_dvd_of_le hXN₀
    rwa [Nat.card_congr eX.toEquiv,
      show Nat.card (alternatingGroup (Fin 5)) = 60 by rw [Nat.card_eq_fintype_card]; rfl] at this
  have hK3 : 3 ≤ Nat.card K := by
    obtain ⟨p, n, hp, hpo, hn, hq⟩ := hK
    rw [hq]
    have : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd (h ▸ hpo) (by decide)
      · obtain ⟨k, hk⟩ := h; have := hp.two_le; omega
    calc 3 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  rcases eq_or_lt_of_le hK3 with h3 | h3
  ·
    obtain ⟨J, -, hJ2, -, ⟨eJ⟩⟩ := CFSG.OddStandard.SmallF3.Omega.sec5sh8_pgl_layer hK eN
    have hJ : Nat.card J = 12 := by
      rw [Nat.card_congr eJ.toEquiv, psl2_card_formula K hK, ← h3]; norm_num
    have hN : Nat.card N₀ = 24 := by rw [← J.index_mul_card, hJ2, hJ]
    rw [hN] at h60; norm_num at h60
  ·
    set N' : Subgroup L := N₀.subgroupOf L
    have e' : N' ≃* PGL2 K := (Subgroup.subgroupOfEquivOfLe hN₀L).trans eN
    obtain ⟨L₀, hL₀n, hL₀N', ⟨e₀⟩⟩ :=
      exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three N' hN₀n K hK h3 e'
    have hF : CFSG.GH74.GLS.IVK.L2Field K := ⟨by obtain ⟨p, n, hp, hpo, -, hq⟩ := hK; rw [hq]; exact hpo.pow, h3⟩
    have hcardN' : Nat.card N' = 2 * Nat.card L₀ := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_congr e₀.toEquiv,
        CFSG.GH74.GLS.IVK.card_pgl2_eq_two_mul hF]
    have hrel : L₀.relIndex N' = 2 := by
      have := Subgroup.relIndex_mul_card (H := L₀) (K := N')
      rw [inf_eq_left.mpr hL₀N', hcardN'] at this
      have hpos : 0 < Nat.card L₀ := Nat.card_pos
      nlinarith
    have hidx : L₀.index = 2 * N'.index := by
      rw [← Subgroup.relIndex_mul_index hL₀N', hrel]
    have hN'idx : N'.index = N₀.relIndex L := rfl
    have hodd' : Odd N'.index := hN'idx ▸ hodd
    obtain ⟨M₂, hM₂n, hM₂idx, -⟩ := exists_normal_index_two_containing_of_index_eq_two_mul_odd
      hL₀n (by rw [hidx]; exact dvd_mul_right 2 _) (by
        rw [hidx]; intro h4
        obtain ⟨k, hk⟩ := hodd'
        rw [hk] at h4; omega)
    set M : Subgroup G := M₂.map L.subtype
    have hML : M ≤ L := Subgroup.map_subtype_le M₂
    have hcM : ⁅L, L⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact ⟨(⟨x, hx⟩ : L) * ⟨y, hy⟩ * (⟨x, hx⟩ : L)⁻¹ * (⟨y, hy⟩ : L)⁻¹,
        commutatorElement_mem_of_index_two hM₂idx _ _, rfl⟩
    have hMrel : M.relIndex L = 2 := by
      rw [Subgroup.relIndex, show M.subgroupOf L = M₂ from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective M₂, hM₂idx]
    have := Subgroup.relIndex_mul_relIndex _ _ _ hcM hML
    rw [hMrel] at this
    rw [← this] at hab
    exact (Nat.not_even_iff_odd.mpr hab) (even_two.mul_left _)

theorem index_le_two_of_commutator_le {D : Set G} (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup G D)
    {M : Subgroup G} [hM : M.Normal] (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ M) :
    M.index ≤ 2 := by
  obtain ⟨d₀, hd₀⟩ := hS.nonempty
  have hle : M ⊔ Subgroup.zpowers d₀ = ⊤ := by
    rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd₀ hx)
    have : g * d₀ * g⁻¹ = (g * d₀ * g⁻¹ * d₀⁻¹) * d₀ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm g d₀))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d₀))
  have hd2 : d₀ * d₀ = 1 := hS.oddT.mul_self_eq_one hd₀
  have h1 : M.index = M.relIndex (Subgroup.zpowers d₀) := by
    rw [← Subgroup.relIndex_sup_left (K := M), hle, Subgroup.relIndex_top_right]
  have h2 := Subgroup.relIndex_mul_card (H := M) (K := Subgroup.zpowers d₀)
  have h3 : Nat.card (Subgroup.zpowers d₀) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, hd2])
  have h4 : 0 < Nat.card (M ⊓ Subgroup.zpowers d₀ : Subgroup G) := Nat.card_pos
  rw [h1]
  nlinarith

theorem three_le_of_isOddPrimePower {q : ℕ} (hq : IsOddPrimePower q) : 3 ≤ q := by
  obtain ⟨p, n, hp, hpo, hn, rfl⟩ := hq
  have : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd (h ▸ hpo) (by decide)
    · obtain ⟨k, hk⟩ := h; have := hp.two_le; omega
  calc 3 ≤ p := this
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn

theorem isOddPrimePower_of_sq {F : Type} [Field F] [Finite F] {q : ℕ}
    (hq : IsOddPrimePower q) (h : Nat.card F ^ 2 = q) : IsOddPrimePower (Nat.card F) := by
  classical
  letI := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hpf : Fact (ringChar F).Prime := ⟨hp⟩
  refine ⟨ringChar F, n, hp, ?_, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨p, m, hp', hpo, -, rfl⟩ := hq
  have hodd : Odd (Nat.card F) := by
    have : Odd (Nat.card F ^ 2) := h ▸ hpo.pow
    exact (Nat.odd_pow_iff two_ne_zero).mp this
  rw [Nat.card_eq_fintype_card, hn] at hodd
  exact (Nat.odd_pow_iff n.ne_zero).mp hodd

theorem card_le_120_of_pgl2 {C : Type} [Group C] [Finite C] {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : IsOddPrimePower (Nat.card F₀)) (h3 : 3 < Nat.card F₀) (φ : C ≃* PGL2 F₀)
    {X : Subgroup C} (eX : X ≃* alternatingGroup (Fin 5)) (ψ : C →* Equiv.Perm (Fin 5))
    (hψ : ∀ c : C, ψ c = 1 → ∀ x ∈ X, c * x = x * c) : Nat.card C ≤ 120 := by
  classical
  obtain ⟨J, hJn, hJ2, hJC, ⟨eJ⟩⟩ := CFSG.OddStandard.SmallF3.Omega.sec5sh8_pgl_layer hF₀ φ
  haveI : IsSimpleGroup J := by
    haveI : IsSimpleGroup (PSL2 F₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact eJ.isSimpleGroup
  have hXJ : X ≤ J := by
    rw [← CFSG.GH74.Generic.S45.a5_perfect eX, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def]
    exact commutatorElement_mem_of_index_two hJ2 x y
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    set M := ψ.ker
    have hMJ : ((M ⊓ J).subgroupOf J).Normal := by
      refine ⟨fun x hx j => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxM, hxJ⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(inferInstance : M.Normal).conj_mem _ hxM j,
        J.mul_mem (J.mul_mem j.2 hxJ) (J.inv_mem j.2)⟩
    rcases hMJ.eq_bot_or_eq_top with h | h
    ·
      have hmJ : m ∈ Subgroup.centralizer (J : Set C) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hc : j * m * j⁻¹ * m⁻¹ ∈ M ⊓ J := Subgroup.mem_inf.mpr
          ⟨M.mul_mem ((inferInstance : M.Normal).conj_mem _ (MonoidHom.mem_ker.mpr hm) j)
            (M.inv_mem (MonoidHom.mem_ker.mpr hm)),
            by rw [show j * m * j⁻¹ * m⁻¹ = j * (m * j⁻¹ * m⁻¹) by group]
               exact J.mul_mem hj (hJn.conj_mem _ (J.inv_mem hj) m)⟩
        have : (⟨_, (Subgroup.mem_inf.mp hc).2⟩ : J) ∈ (M ⊓ J).subgroupOf J := by
          rw [Subgroup.mem_subgroupOf]; exact hc
        rw [h, Subgroup.mem_bot] at this
        have := congrArg Subtype.val this
        simp only [Subgroup.coe_one] at this
        calc j * m = (j * m * j⁻¹ * m⁻¹) * m * j := by group
          _ = m * j := by rw [this, one_mul]
      rw [hJC, Subgroup.mem_bot] at hmJ
      exact (Subgroup.mem_bot).mpr hmJ
    ·
      exfalso
      have hJM : ∀ j ∈ J, ψ j = 1 := fun j hj => by
        have : (⟨j, hj⟩ : J) ∈ (M ⊓ J).subgroupOf J := by rw [h]; trivial
        rw [Subgroup.mem_subgroupOf] at this
        exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp this).1
      have hab : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by
        intro a b
        have := hψ _ (hJM _ (hXJ (eX.symm a).2)) _ (eX.symm b).2
        have h' : eX.symm a * eX.symm b = eX.symm b * eX.symm a := Subtype.ext this
        simpa using congrArg eX h'
      have hnc : ¬ ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by decide +kernel
      exact hnc hab
  calc Nat.card C ≤ Nat.card (Equiv.Perm (Fin 5)) := Nat.card_le_card_of_injective ψ hinj
    _ = 120 := by rw [Nat.card_perm, Nat.card_fin]; rfl

variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem Config.eq_of_normal_psl2 (hQ : Config D u w v z a K₁ S') {L N₀ : Subgroup G}
    [hL : L.Normal] (hL2 : L.index = 2) (hK₁L : K₁ ≤ L) (hN₀L : N₀ ≤ L)
    (hN₀n : (N₀.subgroupOf L).Normal) (hodd : Odd (N₀.relIndex L)) {K : Type} [Field K]
    [Finite K] (hK : IsOddPrimePower (Nat.card K)) (eN : N₀ ≃* PSL2 K) :
    N₀ = L ∧ Subgroup.centralizer (N₀ : Set G) = ⊥ ∧ Nonempty (N₀ ≃* PSL225) := by
  classical
  obtain ⟨eK⟩ := hQ.K₁_A5
  obtain ⟨hz2, hz1, -⟩ := hQ.z_facts
  have hK₁N₀ := le_of_odd_relIndex_of_A5 hN₀L hN₀n hodd hK₁L ⟨eK⟩
  have h60K : Nat.card (alternatingGroup (Fin 5)) = 60 := by rw [Nat.card_eq_fintype_card]; rfl
  have h60 : 60 ∣ Nat.card N₀ := by
    have := Subgroup.card_dvd_of_le hK₁N₀; rwa [Nat.card_congr eK.toEquiv, h60K] at this
  have hK3 : 3 < Nat.card K := by
    rcases eq_or_lt_of_le (three_le_of_isOddPrimePower hK) with h | h
    · exfalso
      rw [Nat.card_congr eN.toEquiv, psl2_card_formula K hK, ← h] at h60
      norm_num at h60
    · exact h
  have hF : CFSG.GH74.GLS.IVK.L2Field K :=
    ⟨by obtain ⟨p, n, hp, hpo, -, hq⟩ := hK; rw [hq]; exact hpo.pow, hK3⟩
  haveI hsimp : IsSimpleGroup N₀ := by
    haveI : IsSimpleGroup (PSL2 K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact eN.isSimpleGroup
  have hnab : ∃ x y : N₀, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by decide +kernel
    refine ⟨⟨_, hK₁N₀ (eK.symm a).2⟩, ⟨_, hK₁N₀ (eK.symm b).2⟩, fun h => hab ?_⟩
    have h' : eK.symm a * eK.symm b = eK.symm b * eK.symm a :=
      Subtype.ext (by simpa using congrArg Subtype.val h)
    simpa using congrArg eK h'
  haveI hN₀G : N₀.Normal :=
    normal_of_simple_of_odd_relIndex hN₀L hN₀n hodd hsimp hK₁L ⟨eK⟩
  have hZ : Subgroup.center N₀ = ⊥ := by
    rcases (inferInstance : (Subgroup.center N₀).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have hx : x ∈ Subgroup.center N₀ := by rw [h]; trivial
      exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)
  have hC := centralizer_eq_bot_of_odd_relIndex hL2 hN₀L hodd hZ hQ.rad hQ.center
  set σ : MulAut N₀ := MulAut.conjNormal z with hσ
  have hσ2 : σ ^ 2 = 1 := by rw [hσ, ← map_pow, pow_two, hz2, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hz1
    have : z ∈ Subgroup.centralizer (N₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro n hn
      have h1 := congrArg (fun τ : MulAut N₀ => ((τ ⟨n, hn⟩ : N₀) : G)) h
      simp only [hσ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc n * z = (z * n * z⁻¹) * z := by rw [h1]
        _ = z * n := by group
    rwa [hC, Subgroup.mem_bot] at this
  set K₁N : Subgroup N₀ := K₁.subgroupOf N₀
  have eK₁N : K₁N ≃* alternatingGroup (Fin 5) := (Subgroup.subgroupOfEquivOfLe hK₁N₀).trans eK
  have hK₁F : K₁N ≤ CFSG.GH74.GLS.fixedSubgroup N₀ σ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    show σ x = x
    apply Subtype.ext
    rw [hσ, MulAut.conjNormal_apply]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hQ.K₁_comm hx)
    rw [← this]; group
  let e₀ : N₀ ≃* CFSG.GH74.GLS.IVK.L2 K := eN.trans (CFSG.GH74.GLS.IVK.L2.equivPSL K).symm
  have hcard25 : Nat.card K = 25 := by
    rcases CFSG.GH74.GLS.SP.Local.fixedSubgroup_cases hF e₀ hσ2 hσ1 with ⟨dd, hdih⟩ |
        ⟨F₀, i₁, i₂, hF₀, ⟨φ⟩⟩
    · exact (not_A5_le_of_isDihedralOrder hdih (X := K₁N.subgroupOf _)
        ⟨(Subgroup.subgroupOfEquivOfLe hK₁F).trans eK₁N⟩).elim
    · letI := i₁
      haveI := i₂
      set C := CFSG.GH74.GLS.fixedSubgroup N₀ σ
      have hF₀odd : IsOddPrimePower (Nat.card F₀) := isOddPrimePower_of_sq hK hF₀
      set XC : Subgroup C := K₁N.subgroupOf C
      have eXC : XC ≃* alternatingGroup (Fin 5) :=
        (Subgroup.subgroupOfEquivOfLe hK₁F).trans eK₁N
      have h60C : 60 ∣ Nat.card C := by
        have := Subgroup.card_subgroup_dvd_card XC
        rwa [Nat.card_congr eXC.toEquiv, h60K] at this
      obtain ⟨J, -, hJ2, -, ⟨eJ⟩⟩ := CFSG.OddStandard.SmallF3.Omega.sec5sh8_pgl_layer hF₀odd φ
      set q := Nat.card F₀ with hq
      have hCcard : Nat.card C = 2 * (q * (q ^ 2 - 1) / 2) := by
        rw [← J.index_mul_card, hJ2, Nat.card_congr eJ.toEquiv, psl2_card_formula F₀ hF₀odd]
      have hq3 := three_le_of_isOddPrimePower hF₀odd
      have hqodd : Odd q := by obtain ⟨p, n, hp, hpo, -, h⟩ := hF₀odd; rw [h]; exact hpo.pow
      have hq3' : 3 < q := by
        rcases eq_or_lt_of_le hq3 with h | h
        · rw [hCcard, ← h] at h60C; norm_num at h60C
        · exact h
      let f : C →* G := N₀.subtype.comp C.subtype
      have hfN : ∀ c : C, f c ∈ Subgroup.normalizer (K₁ : Set G) := by
        intro c
        apply hQ.mem_normalizer_K₁_of_commute
        have hc : σ c = c := c.2
        have h1 := congrArg (fun x : N₀ => (x : G)) hc
        simp only [hσ, MulAut.conjNormal_apply] at h1
        show f c * z = z * f c
        calc f c * z = (z * (f c) * z⁻¹) * z := by rw [show z * f c * z⁻¹ = f c from h1]
          _ = z * f c := by group
      let ψ : C →* Equiv.Perm (Fin 5) := (rhoA5 eK).comp (f.codRestrict _ hfN)
      have hψ : ∀ c : C, ψ c = 1 → ∀ x ∈ XC, c * x = x * c := by
        intro c hc x hx
        have hxK : ((x : N₀) : G) ∈ K₁ := hx
        have h1 := commute_of_rhoA5_eq_one eK (f.codRestrict _ hfN c) hc hxK
        apply Subtype.ext; apply Subtype.ext
        show f c * ((x : N₀) : G) = ((x : N₀) : G) * f c
        calc f c * ((x : N₀) : G) = (f c * x * (f c)⁻¹) * f c := by group
          _ = ((x : N₀) : G) * f c := by rw [show f c * ((x : N₀) : G) * (f c)⁻¹ = x from h1]
      have h120 := card_le_120_of_pgl2 hF₀odd hq3' φ eXC ψ hψ
      rw [hCcard] at h120
      have hq5 : q = 5 := by
        by_contra hne
        have hq7 : 7 ≤ q := by obtain ⟨m, hm⟩ := hqodd; omega
        have : 7 * (7 ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / 2 :=
          Nat.div_le_div_right (Nat.mul_le_mul hq7 (Nat.sub_le_sub_right
            (Nat.pow_le_pow_left hq7 2) 1))
        norm_num at this; omega
      rw [← hF₀, hq5]; norm_num
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K25 := Fintype.ofFinite K25
  have eKK : K ≃+* K25 := FiniteField.ringEquivOfCardEq (K := K) (K' := K25) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard25, card_K25])
  have eN25 : N₀ ≃* PSL225 := eN.trans (psl2RingEquiv eKK)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hLie : CFSG.Blueprint.LieModel N₀ .PSL 2 5 2 := by
    refine Or.inl ⟨by decide, ?_⟩
    exact CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv N₀ 5 2
      (by norm_num) eN25
  have hout := CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.card_outer_L225 hLie
  have hcomm := CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.commutator_le_of_card_outer_dvd_four
    hC hout
  have hidx : N₀.index ≤ 2 := by
    refine index_le_two_of_commutator_le hQ.setup fun x y => hcomm ?_
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rwa [commutatorElement_def] at this
  refine ⟨?_, hC, ⟨eN25⟩⟩
  apply Subgroup.eq_of_le_of_card_ge hN₀L
  have h1 := N₀.index_mul_card
  have h2 := L.index_mul_card
  rw [hL2] at h2
  have hpos : 0 < Nat.card N₀ := Nat.card_pos
  nlinarith

end CFSG.OddTranspositions.QZ
