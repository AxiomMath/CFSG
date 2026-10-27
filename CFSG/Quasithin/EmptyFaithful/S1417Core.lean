module

public import CFSG.Quasithin.EmptyFaithful.S1417Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Fix
public import CFSG.Quasithin.EmptyFaithful.S1417CaseTwo
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.EmptyFaithful.S1412
public import CFSG.Quasithin.EmptyFaithful.S1417Factor
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1417

open scoped Classical

section Core

variable {G : Type} [Group G] [Finite G] {T Mc M V : Subgroup G}

theorem core_basic (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V) :
    V ≤ T ∧ T ≤ M ∧ M ≤ Subgroup.normalizer (V : Set G) ∧ IsSylowTwoOf T M := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hTM : T ≤ M := hM.2
  refine ⟨?_, hTM, hV.2.1, hTM, h.sylow.1, ?_⟩
  · have := le_sylow_of_isTwoReducedIn S (by rw [hS]; exact hTM) hV
    rwa [hS] at this
  · intro hd
    have hidx : (T.subgroupOf M).index ∣ T.index := by
      have := Subgroup.relIndex_dvd_index_of_le hTM
      simpa [Subgroup.relIndex] using this
    exact h.sylow.2 (dvd_trans hd hidx)

theorem core_blocks (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hVe : IsElemAbelian 2 V) (hJ : ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G))
    (hperf : perfectCore M ≤ Subgroup.centralizer (V : Set G)) :
    ∃ I : Finset (Subgroup (MulAut (IntMod V hVe))),
      BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I ∧
        IsSylowTwoOf (autI hVe (thompsonJ T)) (autI hVe (thompsonJ M)) ∧
          (I.card = 1 ∨ I.card = 2) := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  have hJ' : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := fun hh =>
    hJ (le_inf ((iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T).trans hTM) hh)
  obtain ⟨I, hJsyl, hYeq, hcomm, hindep, hnat, hsup, hinf, hindepV, hperm⟩ :=
    B2F.structure_of_not_le_of_quot hVe hV (isSolvable_autI hVe hMN hperf) hT' hJ'
  have hS : BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I :=
    ⟨hYeq, hcomm, hindep, hnat, hsup, hinf, hindepV, hperm⟩
  refine ⟨I, hS, hJsyl, ?_⟩
  have hJMN : thompsonJ M ≤ Subgroup.normalizer (V : Set G) :=
    (iSup₂_le fun _ hA => hA.1 : thompsonJ M ≤ M).trans hMN
  have hr2 : I.card ≤ 2 := hS.card_le_two hVe hMN (pRank_top_le_two h hM.1)
  have hr1 : 1 ≤ I.card := by
    by_contra hlt
    have hI : I = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hJ'
    have hY : autI hVe (thompsonJ M) = ⊥ := by rw [hYeq, hI]; simp
    have h2 : thompsonJ M ≤ Subgroup.centralizer (V : Set G) :=
      (autI_eq_bot_iff hVe hJMN).mp hY
    exact (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT').trans h2
  omega

variable {hVe : IsElemAbelian 2 V} {I : Finset (Subgroup (MulAut (IntMod V hVe)))}

theorem core_Ustar (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hS : BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I) (hr : 1 ≤ I.card) :
    ∃ u ∈ ⨆ L ∈ I, commV L, u ≠ 1 ∧ IntMod.val u ∈ quasithinOmegaOneCenter T := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  obtain ⟨L, hL⟩ := Finset.card_pos.mp hr
  have hne : (⨆ L ∈ I, commV L) ≠ ⊥ := by
    intro hbot
    have h4 := (card_of_actsAsNaturalL2 (hS.nat L hL)).2
    have : commV L = ⊥ := le_bot_iff.mp (hbot ▸ commV_le_iSup hL)
    rw [this, Subgroup.card_bot] at h4
    omega
  exact exists_Z_of_stable h hVe hVT (hTM.trans hMN) hne
    (fun g hg u hu => hS.apply_mem (autI_mono hVe hTM hg) hu)

theorem core_K (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hS : BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I) (hr : 1 ≤ I.card) :
    ∀ (m : G) (hmM : m ∈ M),
      (∀ y ∈ autI hVe (thompsonJ M),
        convI hVe ⟨m, hV.2.1 hmM⟩ * y = y * convI hVe ⟨m, hV.2.1 hmM⟩) → m ∈ Mc := by
  intro m hmM hc
  obtain ⟨u₀, hu₀, hu₁, hu₂⟩ := core_Ustar h hM hV hS hr
  have hmN : m ∈ Subgroup.normalizer (V : Set G) := hV.2.1 hmM
  have hX : convI hVe ⟨m, hmN⟩ ∈ autI hVe M := convI_mem_autI hVe hmM hmN
  have h1 : convI hVe ⟨m, hmN⟩ u₀ = u₀ := hS.apply_eq_of_commute hX hc u₀ hu₀
  have h2 : m * u₀.val * m⁻¹ = u₀.val := by
    have := convI_apply_val hVe ⟨m, hmN⟩ u₀
    rw [h1] at this
    exact this.symm
  have h3 : m ∈ Subgroup.centralizer ({u₀.val} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp h2
  exact centralizer_singleton_le_mc h hu₂ (fun h1 => hu₁ (IntMod.val_injective (by simpa using h1))) h3

theorem core_fix_eq_bot (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hS : BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I)
    (hcard : I.card = 1 ∨ I.card = 2)
    (hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2) :
    fixV (autI hVe (thompsonJ M)) = ⊥ := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hr : 1 ≤ I.card := by omega
  by_contra hFne
  have hJM : thompsonJ M ≤ M := iSup₂_le fun _ hA => hA.1
  have hYX : autI hVe (thompsonJ M) ≤ autI hVe M := autI_mono hVe hJM
  have hXY := conjAut_autI_thompsonJ (V := V) (H := M) hVe
  have hTbar : IsSylowTwoOf (autI hVe T) (autI hVe M) := B2F.isSylowTwoOf_autI hVe hMN hT'
  obtain ⟨z, hz, hz1, hzZ⟩ := exists_Z_of_stable h hVe hVT hTN hFne
    (fun g hg u hu => apply_mem_fixV_of_conj (hXY g (autI_mono hVe hTM hg)) hu)
  obtain ⟨w, hw, hw1, hwZ⟩ := core_Ustar h hM hV hS hr
  have hz1' : z.val ≠ 1 := fun h1 => hz1 (IntMod.val_injective (by simpa using h1))
  have hw1' : w.val ≠ 1 := fun h1 => hw1 (IntMod.val_injective (by simpa using h1))
  have hzw : z ≠ w := by
    intro hzw
    have : z ∈ fixV (autI hVe (thompsonJ M)) ⊓ ⨆ L ∈ I, commV L := ⟨hz, hzw ▸ hw⟩
    rw [hS.inf, Subgroup.mem_bot] at this
    exact hz1 this
  have hMne : M ≠ Mc := by
    rcases hcase with hne | h2
    · exact hne
    · exfalso
      obtain ⟨s, -, -, hsu⟩ := exists_eq_of_card_eq_two h2
      have e1 : z.val = s := (hsu _ hzZ).resolve_left hz1'
      have e2 : w.val = s := (hsu _ hwZ).resolve_left hw1'
      exact hzw (IntMod.val_injective (e1.trans e2.symm))
  have hJMc : thompsonJ M ≤ Mc := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hMN (hJM hy)
    have hconv : convI hVe ⟨y, hyN⟩ z = z := hz _ (convI_mem_autI hVe hy hyN)
    have h2 : y * z.val * y⁻¹ = z.val := by
      have := convI_apply_val hVe ⟨y, hyN⟩ z
      rw [hconv] at this
      exact this.symm
    have h3 : y ∈ Subgroup.centralizer ({z.val} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp h2
    exact centralizer_singleton_le_mc h hzZ hz1' h3
  have hK := core_K h hM hV hS hr
  have hMle : M ≤ Mc := by
    intro m hm
    have hmN : m ∈ Subgroup.normalizer (V : Set G) := hMN hm
    have hX : convI hVe ⟨m, hmN⟩ ∈ autI hVe M := convI_mem_autI hVe hm hmN
    obtain ⟨y', hy', τ, hτ, hcomm⟩ := hS.exists_factor hYX hXY hcard hTbar hX
    obtain ⟨y₀, hy₀, hy₀eq⟩ := (mem_autI hVe).1 hy'
    obtain ⟨t₀, ht₀, ht₀eq⟩ := (mem_autI hVe).1 hτ
    set a : Subgroup.normalizer (V : Set G) := ⟨m, hmN⟩ with ha
    set kN : Subgroup.normalizer (V : Set G) := y₀⁻¹ * a * t₀⁻¹ with hkN
    have hkG : (kN : G) = (y₀ : G)⁻¹ * m * (t₀ : G)⁻¹ := rfl
    have hkM : (kN : G) ∈ M := by
      rw [hkG]
      exact M.mul_mem (M.mul_mem (M.inv_mem (hJM hy₀)) hm) (M.inv_mem (hTM ht₀))
    have hconvk : convI hVe kN = y'⁻¹ * convI hVe a * τ⁻¹ := by
      rw [hkN, map_mul, map_mul, map_inv, map_inv, hy₀eq, ht₀eq]
    have hkMc : (kN : G) ∈ Mc := by
      refine hK (kN : G) hkM fun y'' hy'' => ?_
      have : convI hVe ⟨(kN : G), hV.2.1 hkM⟩ = convI hVe kN := rfl
      rw [this, hconvk]
      exact hcomm y'' hy''
    have hm_eq : m = (y₀ : G) * (kN : G) * (t₀ : G) := by
      rw [hkG]
      group
    rw [hm_eq]
    exact Mc.mul_mem (Mc.mul_mem (hJMc hy₀) hkMc) (h.t_le_mc ht₀)
  exact hMne (hM.1.2 Mc h.mc_max.1 hMle).symm

omit [Finite G] in
theorem ne_mc_of_two_Z {z w : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hw : w ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z ≠ w)
    (hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2) : M ≠ Mc := by
  rcases hcase with hne | h2
  · exact hne
  · exfalso
    obtain ⟨s, -, -, hsu⟩ := exists_eq_of_card_eq_two h2
    exact hzw (((hsu _ hz).resolve_left hz1).trans ((hsu _ hw).resolve_left hw1).symm)

private theorem sup_le_normalizer_left {W : Type*} [CommGroup W] {L₁ L₂ : Subgroup (MulAut W)}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  exact Subgroup.centralizer_le_normalizer (s := (L₁ : Set (MulAut W)))
    (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)

private theorem sup_le_normalizer_right {W : Type*} [CommGroup W] {L₁ L₂ : Subgroup (MulAut W)}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set (MulAut W)) := by
  refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
  exact Subgroup.centralizer_le_normalizer (s := (L₂ : Set (MulAut W)))
    (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)

theorem core_one (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hS : BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I)
    (hJsyl : IsSylowTwoOf (autI hVe (thompsonJ T)) (autI hVe (thompsonJ M)))
    (hone : I.card = 1) (hfix : fixV (autI hVe (thompsonJ M)) = ⊥) (R : Prop) :
    CoreConcl T M V R := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hJM : thompsonJ M ≤ M := iSup₂_le fun _ hA => hA.1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJTN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := hJT.trans hTN
  obtain ⟨L₁, rfl⟩ := Finset.card_eq_one.mp hone
  have hL₁ : L₁ ∈ ({L₁} : Finset (Subgroup (MulAut (IntMod V hVe)))) := Finset.mem_singleton_self L₁
  have hN₁ := hS.nat L₁ hL₁
  have hUtop : commV L₁ = ⊤ := by
    have := hS.sup
    rwa [hfix, bot_sup_eq, iSup_single] at this
  have hYeq : autI hVe (thompsonJ M) = L₁ := by rw [hS.Y_eq, iSup_single (fun L => L)]
  have hL₁top : L₁ = ⊤ := eq_top_of_commV_eq_top hN₁ hUtop
  have hXtop : autI hVe M = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hL₁top, ← hYeq]
    exact autI_mono hVe hJM
  have hcardV : Nat.card V = 4 := by
    have h4 := (card_of_actsAsNaturalL2 hN₁).2
    rw [hUtop, Subgroup.card_top] at h4
    exact h4
  have hY6 : Nat.card (autI hVe (thompsonJ M)) = 6 := by
    rw [hYeq]
    exact (card_of_actsAsNaturalL2 hN₁).1
  have hfixJ : Nat.card (fixV (autI hVe (thompsonJ T))) = 2 :=
    card_fixV_of_card_two hN₁ hUtop (hYeq ▸ hJsyl.1) (card_eq_two_of_isSylowTwoOf hJsyl hY6)
  have hE : Nat.card (omegaOneCenterOf (thompsonJ T) ⊓ V : Subgroup G) = 2 := by
    rw [omegaOneCenterOf_inf_eq hVe hVT, ← card_fixV_autI hVe hJTN]
    exact hfixJ
  have hC : Nat.card (V ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ≤ 2 := by
    rw [← card_fixV_autI hVe hTN]
    have hle : fixV (autI hVe T) ≤ fixV (autI hVe (thompsonJ T)) :=
      fun u hu x hx => hu x (autI_mono hVe hJT hx)
    exact (Subgroup.card_le_of_le hle).trans hfixJ.le
  have hodd : ∀ v : V, (v : G) ∈ Subgroup.centralizer (T : Set G) → v ≠ 1 →
      ∀ g ∈ autOn M V, Odd (orderOf g) → g v = v → g = 1 := by
    intro v _ hv1 g hg hodd hgv
    have hgL : g ∈ L₁ := by rw [hL₁top]; trivial
    exact eq_one_of_odd_of_fixed hN₁ (fun l hl u hu => commV_stable L₁ hl hu) hgL hodd
      (by rw [hUtop]; trivial) hv1 hgv
  exact ⟨Or.inl ⟨hcardV, hXtop, hE⟩, hC, hodd⟩

theorem core_two (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hS : BlockSystem (autI hVe M) (autI hVe (thompsonJ M)) I)
    (hJsyl : IsSylowTwoOf (autI hVe (thompsonJ T)) (autI hVe (thompsonJ M)))
    (htwo : I.card = 2) (hfix : fixV (autI hVe (thompsonJ M)) = ⊥)
    (hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2) (R : Prop) (hR : R) :
    CoreConcl T M V R := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hJM : thompsonJ M ≤ M := iSup₂_le fun _ hA => hA.1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJTN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := hJT.trans hTN
  have hYX : autI hVe (thompsonJ M) ≤ autI hVe M := autI_mono hVe hJM
  have hTbar : IsSylowTwoOf (autI hVe T) (autI hVe M) := B2F.isSylowTwoOf_autI hVe hMN hT'
  obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.mp htwo
  have hL₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hVe)))) := by simp
  have hL₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hVe)))) := by simp
  have hN₁ := hS.nat L₁ hL₁
  have hN₂ := hS.nat L₂ hL₂
  have hc := hS.comm L₁ hL₁ L₂ hL₂ hne
  have hinf : commV L₁ ⊓ commV L₂ = ⊥ := by
    have := hS.indepV L₁ hL₁
    rwa [iSup_pair_ne commV (Ne.symm hne)] at this
  have hLinf : L₁ ⊓ L₂ = ⊥ := by
    have := hS.indep L₁ hL₁
    rwa [iSup_pair_ne (fun L => L) (Ne.symm hne)] at this
  have hUtop : commV L₁ ⊔ commV L₂ = ⊤ := by
    have := hS.sup
    rwa [hfix, bot_sup_eq, iSup_pair] at this
  have hY : autI hVe (thompsonJ M) = L₁ ⊔ L₂ := by
    rw [hS.Y_eq, iSup_pair (fun L => L)]
  have hL₁X : L₁ ≤ autI hVe M := (hS.le_Y hL₁).trans hYX
  have hL₂X : L₂ ≤ autI hVe M := (hS.le_Y hL₂).trans hYX
  have hperm : ∀ g ∈ autI hVe M, (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁) := fun g hg => hS.perm_pair hne hg
  have hcv₁ : ∀ g ∈ autI hVe M, (commV L₁).map g.toMonoidHom = commV (B1.conjAut g L₁) :=
    fun g hg => (hS.perm g hg L₁ hL₁).2
  have hcv₂ : ∀ g ∈ autI hVe M, (commV L₂).map g.toMonoidHom = commV (B1.conjAut g L₂) :=
    fun g hg => (hS.perm g hg L₂ hL₂).2
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : commV L₂ ⊓ commV L₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hU₁ne : commV L₁ ≠ ⊥ := by
    intro hbot
    have h4 := (card_of_actsAsNaturalL2 hN₁).2
    rw [hbot, Subgroup.card_bot] at h4
    omega
  have hU₂ne : commV L₂ ≠ ⊥ := by
    intro hbot
    have h4 := (card_of_actsAsNaturalL2 hN₂).2
    rw [hbot, Subgroup.card_bot] at h4
    omega
  rcases eq_sup_or_exists_swap hN₁ hN₂ hc hLinf hinf hUtop hL₁X hL₂X hperm hcv₁ hcv₂ with
    hXeq | ⟨t, htX, ht2, ht1, ht₁, ht₂, hXt⟩
  ·
    exfalso
    have hfixL₁ : ∀ g ∈ L₁ ⊔ L₂, B1.conjAut g L₁ = L₁ := fun g hg =>
      conjAut_eq_iff_mem_normalizer.mpr (sup_le_normalizer_left hc hg)
    have hfixL₂ : ∀ g ∈ L₁ ⊔ L₂, B1.conjAut g L₂ = L₂ := fun g hg =>
      conjAut_eq_iff_mem_normalizer.mpr (sup_le_normalizer_right hc hg)
    have hst₁ : ∀ g ∈ autI hVe T, ∀ u ∈ commV L₁, g u ∈ commV L₁ := by
      intro g hg u hu
      have hgX : g ∈ autI hVe M := autI_mono hVe hTM hg
      have h1 : g u ∈ (commV L₁).map g.toMonoidHom := ⟨u, hu, rfl⟩
      rw [hcv₁ g hgX, hfixL₁ g (hXeq ▸ hgX)] at h1
      exact h1
    have hst₂ : ∀ g ∈ autI hVe T, ∀ u ∈ commV L₂, g u ∈ commV L₂ := by
      intro g hg u hu
      have hgX : g ∈ autI hVe M := autI_mono hVe hTM hg
      have h1 : g u ∈ (commV L₂).map g.toMonoidHom := ⟨u, hu, rfl⟩
      rw [hcv₂ g hgX, hfixL₂ g (hXeq ▸ hgX)] at h1
      exact h1
    obtain ⟨z₁, hz₁, hz₁1, hz₁Z⟩ := exists_Z_of_stable h hVe hVT hTN hU₁ne hst₁
    obtain ⟨z₂, hz₂, hz₂1, hz₂Z⟩ := exists_Z_of_stable h hVe hVT hTN hU₂ne hst₂
    have hz₁1' : z₁.val ≠ 1 := fun h1 => hz₁1 (IntMod.val_injective (by simpa using h1))
    have hz₂1' : z₂.val ≠ 1 := fun h1 => hz₂1 (IntMod.val_injective (by simpa using h1))
    have hz12 : z₁ ≠ z₂ := by
      intro e
      have : z₁ ∈ commV L₁ ⊓ commV L₂ := ⟨hz₁, e ▸ hz₂⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact hz₁1 this
    have hMne : M ≠ Mc := ne_mc_of_two_Z hz₁Z hz₂Z hz₁1' hz₂1'
      (fun e => hz12 (IntMod.val_injective e)) hcase
    have hMle : M ≤ Mc := by
      intro m hm
      have hmN : m ∈ Subgroup.normalizer (V : Set G) := hMN hm
      have hX : convI hVe ⟨m, hmN⟩ ∈ autI hVe M := convI_mem_autI hVe hm hmN
      have hX' : convI hVe ⟨m, hmN⟩ ∈ L₁ ⊔ L₂ := hXeq ▸ hX
      obtain ⟨l₁, hl₁, l₂, hl₂, hprod⟩ := exists_mul_of_mem_sup_of_commute hc hX'
      have hl₁Y : l₁ ∈ autI hVe (thompsonJ M) := hY ▸ Subgroup.mem_sup_left hl₁
      have hl₂Y : l₂ ∈ autI hVe (thompsonJ M) := hY ▸ Subgroup.mem_sup_right hl₂
      obtain ⟨m₁, hm₁, hm₁eq⟩ := (mem_autI hVe).1 hl₁Y
      obtain ⟨m₂, hm₂, hm₂eq⟩ := (mem_autI hVe).1 hl₂Y
      set a : Subgroup.normalizer (V : Set G) := ⟨m, hmN⟩ with ha
      set kN : Subgroup.normalizer (V : Set G) := (m₁ * m₂)⁻¹ * a with hkN
      have hkconv : convI hVe kN = 1 := by
        rw [hkN, map_mul, map_inv, map_mul, hm₁eq, hm₂eq]
        have : convI hVe a = l₁ * l₂ := hprod.symm
        rw [this]
        group
      have hkC : (kN : G) ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hVe kN).1 hkconv
      have hkMc : (kN : G) ∈ Mc := by
        refine centralizer_singleton_le_mc h hz₁Z hz₁1' ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hkC _ z₁.val_mem).symm
      have hm₁Mc : (m₁ : G) ∈ Mc := by
        have e1 : convI hVe m₁ z₂ = z₂ := by
          rw [hm₁eq]
          exact apply_eq_of_mem_commV_of_commute hc hinf hl₁ hz₂
        have e2 : (m₁ : G) * z₂.val * (m₁ : G)⁻¹ = z₂.val := by
          have := convI_apply_val hVe m₁ z₂
          rw [e1] at this
          exact this.symm
        refine centralizer_singleton_le_mc h hz₂Z hz₂1' ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp e2
      have hm₂Mc : (m₂ : G) ∈ Mc := by
        have e1 : convI hVe m₂ z₁ = z₁ := by
          rw [hm₂eq]
          exact apply_eq_of_mem_commV_of_commute hc' hinf' hl₂ hz₁
        have e2 : (m₂ : G) * z₁.val * (m₂ : G)⁻¹ = z₁.val := by
          have := convI_apply_val hVe m₂ z₁
          rw [e1] at this
          exact this.symm
        refine centralizer_singleton_le_mc h hz₁Z hz₁1' ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp e2
      have hm_eq : m = (m₁ : G) * (m₂ : G) * (kN : G) := by
        simp only [hkN, ha, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hm_eq]
      exact Mc.mul_mem (Mc.mul_mem hm₁Mc hm₂Mc) hkMc
    exact hMne (hM.1.2 Mc h.mc_max.1 hMle).symm
  ·
    obtain ⟨τ, hτ, hτ1⟩ := exists_swap_mem_of_isSylowTwoOf hTbar htX
      (by rw [ht₁]; exact Ne.symm hne) hperm
    have hτX : τ ∈ autI hVe M := hTbar.1 hτ
    have hτs : B1.conjAut τ L₁ = L₂ ∧ B1.conjAut τ L₂ = L₁ := by
      rcases hperm τ hτX with ⟨h, -⟩ | h
      · exact absurd h hτ1
      · exact h
    have hτS := conjAut_autI_thompsonJ (V := V) (H := T) hVe τ hτ
    have hJsyl' : IsSylowTwoOf (autI hVe (thompsonJ T)) (L₁ ⊔ L₂) := hY ▸ hJsyl
    have hU₁ : ∀ u ∈ commV L₁, τ u ∈ commV L₂ := fun u hu => by
      have h1 : τ u ∈ (commV L₁).map τ.toMonoidHom := ⟨u, hu, rfl⟩
      rw [hcv₁ τ hτX, hτs.1] at h1
      exact h1
    have hU₂ : ∀ u ∈ commV L₂, τ u ∈ commV L₁ := fun u hu => by
      have h1 : τ u ∈ (commV L₂).map τ.toMonoidHom := ⟨u, hu, rfl⟩
      rw [hcv₂ τ hτX, hτs.2] at h1
      exact h1
    obtain ⟨hcard4, a₁, ha₁, a₂, ha₂, ha₁1, ha₂1, hfixT⟩ := fixV_swap hJsyl' hN₁ hN₂ hc hLinf
      hinf hUtop (autI_mono hVe hJT) hτ hτS hτs.1 hτs.2 hU₁ hU₂
    have hE4 : Nat.card (omegaOneCenterOf (thompsonJ T) ⊓ V : Subgroup G) = 4 := by
      rw [omegaOneCenterOf_inf_eq hVe hVT, ← card_fixV_autI hVe hJTN]
      exact hcard4
    have hC : Nat.card (V ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ≤ 2 := by
      rw [← card_fixV_autI hVe hTN]
      have hsub : ((fixV (autI hVe T) : Subgroup (IntMod V hVe)) : Set (IntMod V hVe)) ⊆
          ↑({1, a₁ * a₂} : Finset (IntMod V hVe)) := by
        intro w hw
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact hfixT w hw
      have h1 : Nat.card (fixV (autI hVe T)) =
          ((fixV (autI hVe T) : Subgroup (IntMod V hVe)) : Set (IntMod V hVe)).ncard :=
        Nat.card_coe_set_eq _
      rw [h1]
      calc _ ≤ (↑({1, a₁ * a₂} : Finset (IntMod V hVe)) : Set (IntMod V hVe)).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ({1, a₁ * a₂} : Finset (IntMod V hVe)).card := Set.ncard_coe_finset _
        _ ≤ 2 := Finset.card_le_two
    have hodd : ∀ v : V, (v : G) ∈ Subgroup.centralizer (T : Set G) → v ≠ 1 →
        ∀ g ∈ autOn M V, Odd (orderOf g) → g v = v → g = 1 := by
      intro v hvC hv1 g hg hodd hgv
      have hvfix : (v : IntMod V hVe) ∈ fixV (autI hVe T) := (mem_fixV_autI hVe hTN _).2 hvC
      rcases hfixT v hvfix with h1 | h1
      · exact absurd h1 hv1
      · rw [h1] at hgv
        have hgL : g ∈ L₁ ⊔ L₂ := mem_of_sq_mem_of_odd
          (sq_mem_sup hN₁ hN₂ hc hinf hUtop hperm hcv₁ hcv₂ hg) hodd
        exact eq_one_of_odd_of_fixed_pair hN₁ hN₂ hc hLinf hinf ha₁ ha₂ ha₁1 ha₂1 hgL hodd hgv
    have hcv₁' : (commV L₁).map t.toMonoidHom = commV L₂ := by
      rw [hcv₁ t htX, ht₁]
    have hcv₂' : (commV L₂).map t.toMonoidHom = commV L₁ := by
      rw [hcv₂ t htX, ht₂]
    exact ⟨Or.inr (caseTwo_core hVe hMN hN₁ hN₂ hc hLinf hinf hUtop hL₁X hL₂X htX ht2 ht1 ht₁
      hXt hY hcv₁' hcv₂' hE4 R hR), hC, hodd⟩

theorem core (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hJ : ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G))
    (hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2)
    (hperf : perfectCore M ≤ Subgroup.centralizer (V : Set G)) (R : Prop) (hR : R) :
    CoreConcl T M V R := by
  obtain ⟨I, hS, hJsyl, hcard⟩ := core_blocks h hM hV hV.2.2.1 hJ hperf
  have hfix := core_fix_eq_bot h hM hV hS hcard hcase
  rcases hcard with h1 | h2
  · exact core_one h hM hV hS hJsyl h1 hfix R
  · exact core_two h hM hV hS hJsyl h2 hfix hcase R hR

end Core

end S1417

end CFSG.Quasithin
