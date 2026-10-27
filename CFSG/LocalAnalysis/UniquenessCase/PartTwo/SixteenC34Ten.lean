module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def R1110Core (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V →
    ∀ [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal],
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M) →
      pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ =
          F11.barImage11 D.M V₀ V (P ⊓ ⁅D.M, D.M⁆) ∧
      (IsCyclic ↥(P ⊓ F11.CTilde D.M V₀ V) ∧
        ⁅P ⊓ ⁅D.M, D.M⁆, P ⊓ F11.CTilde D.M V₀ V⁆ = ⊥) ∧
      ∀ n : ℕ, 1 < n → ∀ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal →
        IsElemAbelian p Xbar → Nat.card Xbar = p ^ n →
        Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ →
        (∀ x ∈ F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar), x ^ p = 1) ∧
          (IsMulCommutative (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) ∨
            (Nat.card ↥⁅F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar),
                F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)⁆ = p ∧
              ⁅F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar),
                F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)⁆ ≤
                F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ⊓
                  centralizer ((F11.Omega1p p
                    (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) : Subgroup G) : Set G))) ∧
          p ^ n ≤ Nat.card
            (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) ∧
          n / 2 + 1 ≤ CFSG.Open.pRank p
            (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar))

theorem s16c34_ten_part1 (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V)
    (h118 : C118 D V₀ V) [hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆ =
      F11.barImage11 D.M V₀ V (P ⊓ ⁅D.M, D.M⁆) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hn, hO, -⟩ := ElevenNine.hyp11_ctilde D hV
  haveI hNn : (barImage D.M (F11.CTilde D.M V₀ V)).Normal := uc22p22u_barImage_normal hn
  obtain ⟨φ, hφs, hφk, hφπ⟩ := uc22p22u_exists_phi (M := D.M) (X := F11.CTilde D.M V₀ V) hO
  have hbar := uc22p22u_barImage_inf_commutator hp hp2 hP
  have key := uc22p22u_pCore_commutator_le_image φ hφs (barImage D.M (F11.CTilde D.M V₀ V)) hφk p
    hp h118
  apply le_antisymm
  · intro b hb
    obtain ⟨y, hy, hφy⟩ := key b hb
    rw [← hbar] at hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    rw [← hφy, hφπ]
    exact ⟨m, hm, rfl⟩
  · set T : Subgroup (F11.MBar11 D.M V₀ V) := ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ with hT
    set S : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V (P ⊓ ⁅D.M, D.M⁆) with hS
    have hSφ : S = (CFSG.pCore p (Bar2 D.M) ⊓ ⁅(⊤ : Subgroup (Bar2 D.M)), ⊤⁆).map φ := by
      rw [← hbar]
      ext b
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨uc22p21cPi D.M m, uc22p21c_mem_barImage.2 ⟨m, hm, rfl⟩, hφπ m⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
        exact ⟨m, hm, (hφπ m).symm⟩
    haveI : (CFSG.pCore p (Bar2 D.M) ⊓ ⁅(⊤ : Subgroup (Bar2 D.M)), ⊤⁆).Normal := by
      haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
      infer_instance
    haveI hSn : S.Normal := by
      rw [hSφ]
      exact Subgroup.Normal.map inferInstance φ hφs
    have hSle : S ≤ T := by
      rw [hSφ, hT, ← Subgroup.map_top_of_surjective φ hφs, ← Subgroup.map_commutator]
      exact Subgroup.map_mono inf_le_right
    have hSp : IsPGroup p ↥S := by
      have h0 : IsPGroup p ↥(CFSG.pCore p (Bar2 D.M) ⊓ ⁅(⊤ : Subgroup (Bar2 D.M)), ⊤⁆) :=
        (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).to_inf_left
      rw [hSφ]
      exact h0.map φ
    exact uc22p22u_le_pCoreOf S T hSp hSle

theorem s16c34_ten_part2 (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V)
    (h116 : C116 D V₀ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    IsCyclic ↥(P ⊓ F11.CTilde D.M V₀ V) ∧
      ⁅P ⊓ ⁅D.M, D.M⁆, P ⊓ F11.CTilde D.M V₀ V⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPM, hbar, hP2⟩ := uc22p22u_sylow_O2p hp hp2 hP
  obtain ⟨hn, -, -⟩ := ElevenNine.hyp11_ctilde D hV
  haveI hNn : (barImage D.M (F11.CTilde D.M V₀ V)).Normal := uc22p22u_barImage_normal hn
  obtain ⟨hcyc, hcomm⟩ := h116
  set X₀ : Subgroup G := F11.CTilde D.M V₀ V with hX₀
  set N : Subgroup (Bar2 D.M) := barImage D.M X₀ with hN
  set F : Subgroup (Bar2 D.M) := (CFSG.fittingSubgroup ↥N).map N.subtype with hF
  have hFcyc : IsCyclic ↥F := (uc22p22u_isCyclic_map_iff _ N.subtype_injective _).2 hcyc
  have hUM : P ⊓ X₀ ≤ D.M := inf_le_left.trans hPM
  have hA : ∀ x : ↥D.M, (x : G) ∈ P ⊓ X₀ → uc22p21cPi D.M x ∈ F := by
    intro x hx
    have h1 : uc22p21cPi D.M x ∈ CFSG.pCore p (Bar2 D.M) :=
      hbar ▸ uc22p21c_mem_barImage.2 ⟨x, hx.1, rfl⟩
    have h2 : uc22p21cPi D.M x ∈ N := uc22p21c_mem_barImage.2 ⟨x, hx.2, rfl⟩
    haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
    set R : Subgroup (Bar2 D.M) := CFSG.pCore p (Bar2 D.M) ⊓ N with hR
    haveI hRn : R.Normal := inferInstance
    have hRp : IsPGroup p ↥R := (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).to_inf_left
    have hRN : (R.subgroupOf N).Normal := hRn.subgroupOf N
    have hRp' : IsPGroup p ↥(R.subgroupOf N) := hRp.comap_subtype
    have hRnil : Group.IsNilpotent ↥(R.subgroupOf N) := hRp'.isNilpotent
    have hle : R.subgroupOf N ≤ CFSG.fittingSubgroup ↥N := le_sSup ⟨hRN, hRnil⟩
    exact ⟨⟨uc22p21cPi D.M x, h2⟩, hle (Subgroup.mem_subgroupOf.2 ⟨h1, h2⟩), rfl⟩
  have hker : ∀ a b : ↥(P ⊓ X₀), uc22p21cPi D.M (Subgroup.inclusion hUM a) =
      uc22p21cPi D.M (Subgroup.inclusion hUM b) → a = b := by
    intro a b hab
    have h1 : (Subgroup.inclusion hUM a)⁻¹ * Subgroup.inclusion hUM b ∈ CFSG.pCore 2 ↥D.M :=
      (QuotientGroup.eq_one_iff _).1 (by
        change uc22p21cPi D.M _ = 1
        rw [map_mul, map_inv, hab, inv_mul_cancel])
    have h2 : ((a : G))⁻¹ * (b : G) ∈ P ⊓ pCoreOf 2 D.M :=
      ⟨(P ⊓ X₀).mul_mem ((P ⊓ X₀).inv_mem a.2) b.2 |>.1, ⟨_, h1, rfl⟩⟩
    rw [hP2, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  refine ⟨?_, ?_⟩
  · let g : ↥(P ⊓ X₀) →* ↥F := ((uc22p21cPi D.M).comp (Subgroup.inclusion hUM)).codRestrict F
      fun a => hA (Subgroup.inclusion hUM a) a.2
    haveI := hFcyc
    exact isCyclic_of_injective g fun a b hab => hker a b (congrArg Subtype.val hab)
  · rw [← le_bot_iff, Subgroup.commutator_le]
    intro q hq u hu
    have hqM : q ∈ D.M := hPM hq.1
    have huM : u ∈ D.M := hUM hu
    have hq' : uc22p21cPi D.M ⟨q, hqM⟩ ∈
        ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ := by
      rw [← uc22p22u_map_commutator]
      exact ⟨⟨q, hqM⟩, (uc22p22u_mem_commutator_iff ⟨q, hqM⟩).1 hq.2, rfl⟩
    have hcen := Subgroup.mem_centralizer_iff.1 (hcomm hq') _ (hA ⟨u, huM⟩ hu)
    have h1 : ⁅(⟨q, hqM⟩ : ↥D.M), ⟨u, huM⟩⁆ ∈ CFSG.pCore 2 ↥D.M := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change uc22p21cPi D.M _ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 hcen.symm
    have h2 : ⁅q, u⁆ ∈ P ⊓ pCoreOf 2 D.M := by
      refine ⟨?_, ⟨_, h1, rfl⟩⟩
      have hu' : u ∈ P := hu.1
      have : ⁅q, u⁆ = q * u * q⁻¹ * u⁻¹ := rfl
      rw [this]
      exact P.mul_mem (P.mul_mem (P.mul_mem hq.1 hu') (P.inv_mem hq.1)) (P.inv_mem hu')
    rw [hP2] at h2
    exact h2

theorem s16c34_ten_tdata (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V)
    (h116 : C116 D V₀ V) (h118 : C118 D V₀ V)
    [hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M))
    {Xbar : Subgroup (F11.MBar11 D.M V₀ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆)
    {T Z : Subgroup G} (hT : T = P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)
    (hZ : Z = T ⊓ F11.CTilde D.M V₀ V) :
    IsPGroup p ↥T ∧ IsCyclic ↥Z ∧ Z ≤ T ∧ ⁅T, T⁆ ≤ Z ∧ ⁅T, Z⁆ = ⊥ ∧ (∀ t ∈ T, t ^ p ∈ Z) ∧
      T ≤ D.M ∧ F11.barImage11 D.M V₀ V T = Xbar := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPM, -, -⟩ := uc22p22u_sylow_O2p hp hp2 hP
  have hPp : IsPGroup p ↥P := (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.1
  have h1 := s16c34_ten_part1 D hV h118 hp hp2 hP
  obtain ⟨hcyc, hcent⟩ := s16c34_ten_part2 D hV h116 hp hp2 hP
  have hTP : T ≤ P := by rw [hT]; exact inf_le_left.trans inf_le_left
  have hTQ : T ≤ P ⊓ ⁅D.M, D.M⁆ := by rw [hT]; exact inf_le_left
  have hTM : T ≤ D.M := hTP.trans hPM
  have hZT : Z ≤ T := by rw [hZ]; exact inf_le_left
  have hZP : Z ≤ P ⊓ F11.CTilde D.M V₀ V := by
    rw [hZ]
    exact le_inf (inf_le_left.trans hTP) inf_le_right
  have hmemT : ∀ t ∈ T, ∃ h : t ∈ D.M,
      (QuotientGroup.mk ⟨t, h⟩ : F11.MBar11 D.M V₀ V) ∈ Xbar := by
    intro t ht
    rw [hT] at ht
    exact uc22p22u_mem_barPreimage11.1 ht.2
  refine ⟨hPp.to_le hTP, ?_, hZT, ?_, ?_, ?_, hTM, ?_⟩
  · haveI := hcyc
    exact isCyclic_of_injective (Subgroup.inclusion hZP) (Subgroup.inclusion_injective hZP)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨haM, ha'⟩ := hmemT a ha
    obtain ⟨hbM, hb'⟩ := hmemT b hb
    have hc := hXe.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩
    have hc' : (QuotientGroup.mk ⟨a, haM⟩ : F11.MBar11 D.M V₀ V) * QuotientGroup.mk ⟨b, hbM⟩ =
        QuotientGroup.mk ⟨b, hbM⟩ * QuotientGroup.mk ⟨a, haM⟩ := congrArg Subtype.val hc
    have h2 : (QuotientGroup.mk ⁅(⟨a, haM⟩ : ↥D.M), ⟨b, hbM⟩⁆ : F11.MBar11 D.M V₀ V) = 1 := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply]
      exact commutatorElement_eq_one_iff_commute.2 hc'
    have h3 : ⁅a, b⁆ ∈ F11.CTilde D.M V₀ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using this
    rw [hZ]
    refine ⟨?_, h3⟩
    have : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [this]
    exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)
  · exact le_bot_iff.1 ((Subgroup.commutator_mono hTQ hZP).trans hcent.le)
  · intro t ht
    obtain ⟨htM, ht'⟩ := hmemT t ht
    have h2 : (QuotientGroup.mk (⟨t, htM⟩ ^ p : ↥D.M) : F11.MBar11 D.M V₀ V) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hXe.2 _ ht'
    have h3 : t ^ p ∈ F11.CTilde D.M V₀ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf] using this
    rw [hZ]
    exact ⟨T.pow_mem ht p, h3⟩
  · apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      obtain ⟨hmM, hm'⟩ := hmemT _ hm
      exact hm'
    · intro q hq
      have hq1 : q ∈ pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ :=
        uc22p22u_le_pCoreOf Xbar _ (CFSG.Open.IsElemAbelian.isPGroup hXe) hXle hq
      rw [h1] at hq1
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq1
      refine uc22p22u_mem_barImage11.2 ⟨m, ?_, rfl⟩
      rw [hT]
      exact ⟨hm, uc22p22u_mem_barPreimage11.2 ⟨m.2, hq⟩⟩

theorem s16c34_ten_part3a (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V)
    (h116 : C116 D V₀ V) (h118 : C118 D V₀ V)
    [hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) {n : ℕ} (hn : 1 < n)
    {Xbar : Subgroup (F11.MBar11 D.M V₀ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXc : Nat.card Xbar = p ^ n)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆) :
    (∀ x ∈ F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar), x ^ p = 1) ∧
      (IsMulCommutative (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) ∨
        (Nat.card ↥⁅F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar),
            F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)⁆ = p ∧
          ⁅F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar),
              F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)⁆ ≤
            F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ⊓
              centralizer ((F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) :
                Subgroup G) : Set G))) ∧
      p ^ n ≤ Nat.card (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) ∧
      n / 2 + 1 ≤
        CFSG.Open.pRank p (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) := by
  obtain ⟨hTp, hZc, hZT, hcomm, hcent, hpow, hTM, hbar⟩ :=
    s16c34_ten_tdata D hV h116 h118 hp hp2 hP hXe hXle
    (T := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)
    (Z := (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ⊓ F11.CTilde D.M V₀ V) rfl rfl
  have hcard := uc22p22u_card_eq_barImage11_mul (M := D.M) (V₀ := V₀) (V := V) hTM
  rw [hbar, hXc] at hcard
  exact uc22p22u_twostep_bundle hp hp2 hTp hZc hZT hcomm hcent hpow hn hcard

theorem r1110Core_holds (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D) (h111 : F11.R111 D)
    (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) : R1110Core D := by
  intro V₀ V hV hNorm p hp hp2 P hP
  have h116 := ElevenNine.c116_of_hyp11 D hSig h61 h63 h77 h111 h112 hV
  have h117 := ElevenNine.c117_of_hyp11 D h869 hV
  have h118 := ElevenNine.c118_of_hyp11 hThin hCyc D hV h116 h117
  refine ⟨s16c34_ten_part1 D hV h118 hp hp2 hP, s16c34_ten_part2 D hV h116 hp hp2 hP, ?_⟩
  intro n hn Xbar hXn hXe hXc hXle
  exact s16c34_ten_part3a D hV h116 h118 hp hp2 hP hn hXe hXc hXle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
