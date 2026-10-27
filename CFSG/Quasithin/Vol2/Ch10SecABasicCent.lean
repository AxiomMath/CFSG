module

public import CFSG.Quasithin.Vol2.Ch10SecABasicProd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conjugate_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) :
    CFSG.conjugate X g ≤ CFSG.conjugate Y g :=
  Subgroup.map_mono h

theorem le_normalizer_centralizer {X V : Subgroup G} (h : X ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have key : ∀ x ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      x * c * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hx) v).mp hv
    rw [inv_inv] at hv'
    have := hc _ hv'
    calc v * (x * c * x⁻¹) = x * ((x⁻¹ * v * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * v * x)) * x⁻¹ := by rw [this]
      _ = x * c * x⁻¹ * v := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x (h hx) c, fun hc => ?_⟩
  have := key x⁻¹ ((Subgroup.normalizer _).inv_mem (h hx)) _ hc
  simpa [mul_assoc] using this

theorem pCoreOf_conjugate [Finite G] (K : Subgroup G) (g : G) :
    pCoreOf 2 (CFSG.conjugate K g) = CFSG.conjugate (pCoreOf 2 K) g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (K : Subgroup G) (g : G),
      CFSG.conjugate (pCoreOf 2 K) g ≤ pCoreOf 2 (CFSG.conjugate K g) := by
    intro K g
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (conjugate_mono (Subgroup.map_subtype_le _) g) ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).map _)
    intro y hy
    rw [mem_conjugate_iff] at hy
    rw [← conjugate_eq_self_iff, conjugate_conjugate]
    have hgy : g * y = (g * y * g⁻¹) * g := by group
    rw [hgy, ← conjugate_conjugate,
      conjugate_eq_self_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hy)]
  refine le_antisymm ?_ (key K g)
  have h := conjugate_mono (key (CFSG.conjugate K g) g⁻¹) g
  rwa [conjugate_conjugate, conjugate_conjugate, inv_mul_cancel, conjugate_one, mul_inv_cancel,
    conjugate_one] at h

variable [Finite G] {T L I : Subgroup G}

theorem eq_of_forall_mul_mem_pCoreOf (hf : quasithinIsFaithfulLocal T L) {D : Subgroup G}
    (hDL : D ≤ L) (hn : L ≤ Subgroup.normalizer (D : Set G))
    (hsup : ∀ x ∈ L, ∃ d ∈ D, d⁻¹ * x ∈ pCoreOf 2 L) : D = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (D.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr hn
  refine hf.2.1 D hDL this fun x hx => ?_
  obtain ⟨d, hd, ho⟩ := hsup x hx
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, ho⟩
  have hk' : (d⁻¹ * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have hdx : d⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hDL hd)) hx
  have e1 : ((⟨x, hx⟩ : ↥L) : ↥L ⧸ D.subgroupOf L) = ((⟨d⁻¹ * x, hdx⟩ : ↥L) : _) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : x⁻¹ * d⁻¹ * x⁻¹⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem (hn hx)) _).mp (D.inv_mem hd)
    simpa [mul_assoc] using this
  have e2 : (((⟨x, hx⟩ : ↥L) ^ 2 ^ k : ↥L) : ↥L ⧸ D.subgroupOf L) = 1 := by
    rw [QuotientGroup.mk_pow, e1, ← QuotientGroup.mk_pow]
    rw [show (⟨d⁻¹ * x, hdx⟩ : ↥L) ^ 2 ^ k = 1 from Subtype.ext (by simpa using hk')]
    rfl
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at e2
  simpa using e2

theorem false_of_mem_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {y : G} (hyL : y ∈ L)
    (hyC : y ∈ Subgroup.centralizer (fsuVM T L I : Set G)) (hyO : y ∉ pCoreOf 2 L) : False := by
  have hs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  set D := L ⊓ Subgroup.centralizer (fsuVM T L I : Set G)
  have hDL : D ≤ L := inf_le_left
  have hn : L ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.normalizer (L : Set G) ⊓
        Subgroup.normalizer (Subgroup.centralizer (fsuVM T L I : Set G) : Set G) :=
      ⟨Subgroup.le_normalizer hx,
        le_normalizer_centralizer ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)) hx⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf hx'
  have : (D.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr hn
  have hnorm := (this.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _))
  have htop : (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    refine (hs.eq_bot_or_eq_top_of_normal _).resolve_left fun hbot => hyO ?_
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨y, hyL⟩) ∈
        (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      ⟨⟨y, hyL⟩, ⟨hyL, hyC⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, mk_eq_one_iff] at hmem
    exact hmem
  have hDeq : D = L := eq_of_forall_mul_mem_pCoreOf hyp.fsu.faithful hDL hn fun x hx => by
    have hx' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩) ∈
        (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdx⟩ := hx'
    refine ⟨d, hd, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← subgroupOf_pCoreOf,
      Subgroup.mem_subgroupOf] at hdx
    simpa using hdx
  apply commutator_fsuVM_ne_bot hyp.fsu
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  intro x hx
  rw [← hDeq] at hx
  exact hx.2

theorem fsuL0_inf_centralizer_le (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) :
    fsuL0 T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨φ, -, hk, hL, hLt⟩ := exists_fsuL0_prod h37 h38 hyp ht htn
  have hloc := hyp.fsu.maximal.1
  have hNC := le_normalizer_centralizer (fsuL0_le_normalizer_fsuVM T L I)
  intro x hx
  by_contra hxO
  have hφ : φ ⟨x, hx.1⟩ ≠ 1 := fun h => hxO (by
    rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf] at h
    exact h)
  have hcC : ∀ y ∈ fsuL0 T L, ⁅x, y⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro y hy
    rw [commutatorElement_def]
    have h1 : y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hNC hy) _).mp ((Subgroup.centralizer _).inv_mem hx.2)
    simpa [mul_assoc] using (Subgroup.centralizer _).mul_mem hx.2 h1
  by_cases ha : (φ ⟨x, hx.1⟩).1 = 1
  · have hb : (φ ⟨x, hx.1⟩).2 ∉ Subgroup.center _ := by
      rw [center_quot_conjugate_eq_bot h37 h38 hyp ht htn, Subgroup.mem_bot]
      exact fun hb => hφ (Prod.ext ha hb)
    rw [Subgroup.mem_center_iff] at hb
    push Not at hb
    obtain ⟨c, hc⟩ := hb
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hlL0 : l ∈ fsuL0 T L := conjugate_le_fsuL0 ht hl
    have hyLt : ⁅x, l⁆ ∈ CFSG.conjugate L t := by
      rw [commutatorElement_def]
      have h1 : x * l * x⁻¹ ∈ CFSG.conjugate L t := (Subgroup.mem_normalizer_iff.mp
        (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht) hx.1) l).mp hl
      exact (CFSG.conjugate L t).mul_mem h1 ((CFSG.conjugate L t).inv_mem hl)
    have hval : φ ⟨⁅x, l⁆, conjugate_le_fsuL0 ht hyLt⟩ =
        φ ⁅(⟨x, hx.1⟩ : ↥(fsuL0 T L)), ⟨l, hlL0⟩⁆ := rfl
    rw [hLt _ hyLt, map_commutatorElement, hLt l hl] at hval
    have hyO : ⁅x, l⁆ ∉ pCoreOf 2 (CFSG.conjugate L t) := by
      intro hyO
      have h2 := congrArg Prod.snd hval
      rw [(mk_eq_one_iff (⟨_, hyLt⟩ : ↥(CFSG.conjugate L t))).mpr hyO] at h2
      have h3 : ⁅(φ ⟨x, hx.1⟩).2, ((⟨l, hl⟩ : ↥(CFSG.conjugate L t)) :
          ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t))⁆ = 1 := by
        simpa [commutatorElement_def] using h2.symm
      exact hc (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    refine false_of_mem_centralizer h37 h38 hyp (y := t * ⁅x, l⁆ * t⁻¹)
      (mem_conjugate_iff.mp hyLt) ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_centralizer (le_normalizer_fsuVM T L I) ht) _).mp (hcC l hlL0))
      fun hO => hyO ?_
    rw [pCoreOf_conjugate, mem_conjugate_iff]
    exact hO
  · have ha' : (φ ⟨x, hx.1⟩).1 ∉ Subgroup.center _ := by
      rw [center_quot_eq_bot h37 h38 hyp, Subgroup.mem_bot]
      exact ha
    rw [Subgroup.mem_center_iff] at ha'
    push Not at ha'
    obtain ⟨c, hc⟩ := ha'
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hlL0 : l ∈ fsuL0 T L := le_fsuL0 T L hl
    have hyL : ⁅x, l⁆ ∈ L := by
      rw [commutatorElement_def]
      have h1 : x * l * x⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (fsuL0_le_normalizer hloc hx.1) l).mp hl
      exact L.mul_mem h1 (L.inv_mem hl)
    have hval : φ ⟨⁅x, l⁆, le_fsuL0 T L hyL⟩ = φ ⁅(⟨x, hx.1⟩ : ↥(fsuL0 T L)), ⟨l, hlL0⟩⁆ := rfl
    rw [hL _ hyL, map_commutatorElement, hL l hl] at hval
    refine false_of_mem_centralizer h37 h38 hyp hyL (hcC l hlL0) fun hyO => ?_
    have h2 := congrArg Prod.fst hval
    rw [(mk_eq_one_iff (⟨_, hyL⟩ : ↥L)).mpr hyO] at h2
    have h3 : ⁅(φ ⟨x, hx.1⟩).1, ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)⁆ = 1 := by
      simpa [commutatorElement_def] using h2.symm
    exact hc (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

end CFSG.Quasithin.Vol2.Ch10.SecA
