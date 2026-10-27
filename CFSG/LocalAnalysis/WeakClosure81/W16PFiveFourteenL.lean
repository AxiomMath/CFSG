module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSixC
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoB
public import CFSG.LocalAnalysis.WeakClosure81.TwelveEight
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem Setting12Two.exists_cartan_lifts (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) :
    ∃ C : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤),
      C ≤ M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) ∧ Nat.card C = 2 ^ n - 1 ∧
      ∀ δ ∈ C, δ ≠ 1 → ∃ y : G, y ∈ M ∧ Odd (orderOf y) ∧
        QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤) y = δ ∧
        fixMod (cE ρ.range) (ρ y) ⊓ commSub ρ.range ≤ cE ρ.range := by
  obtain ⟨i, S, t, -, hMS, hc⟩ := h.exists_benderCore
  have hCle : cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t ≤
      M.map (QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)) := by
    rw [hMS]
    exact cartan_le_borel (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t
  refine ⟨cartan (S : Subgroup (G ⧸ CFSG.Quasithin.kerIn M ⊤)) t, hCle, ?_, ?_⟩
  · rw [hc.card_cartan, mul_one]
  · intro δ hδC hδ1
    have hinv : t * δ * t = δ⁻¹ :=
      (hc.mem_commutator_cartan_iff.mp (hc.cartan_eq_commutator rfl ▸ hδC)).2
    have hv2 : (t * δ) * (t * δ) = 1 := by
      calc (t * δ) * (t * δ) = (t * δ * t) * δ := by group
        _ = δ⁻¹ * δ := by rw [hinv]
        _ = 1 := inv_mul_cancel δ
    have huv : t * (t * δ) = δ := by
      calc t * (t * δ) = (t * t) * δ := by group
        _ = δ := by rw [hc.sq_eq_one, one_mul]
    have hodd : Odd (orderOf (t * (t * δ))) := by
      rw [huv]
      exact Odd.of_dvd_nat hc.odd_card_cartan (Subgroup.orderOf_dvd_natCard _ hδC)
    have huv1 : t * (t * δ) ≠ 1 := by rw [huv]; exact hδ1
    obtain ⟨y, hyodd, hy, hyfix⟩ :=
      Setting12Two.exists_odd_fix h hA ρ hq hc.sq_eq_one hv2 hodd huv1
    refine ⟨y, ?_, hyodd, ?_, hyfix⟩
    · rw [b12_TwelveBar_mem_map_iff h, hy, huv]
      exact hCle hδC
    · rw [hy, huv]

theorem Setting12Two.mem_fixSub_range_of_fix (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) {y : G}
    (hy : fixMod (cE ρ.range) (ρ y) ⊓ commSub ρ.range ≤ cE ρ.range) {v : V}
    (hv : v ∈ fixSub (A.map ρ)) (hyv : ρ y v = v) : v ∈ fixSub ρ.range := by
  obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp
    (Setting12Two.fixSub_le_commSub_sup_fixSub h hA ρ hq hv)
  have hcG : ρ y c = c := hc (ρ y) (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
  have hwfix : ρ y w = w := by
    have h1 : ρ y (w + c) = w + c := by rw [hwc]; exact hyv
    rw [map_add, hcG] at h1
    exact add_right_cancel h1
  have hwE : w ∈ commSub ρ.range :=
    commSub_mono (A.map ρ) ρ.range (Subgroup.map_le_range ρ A) hw
  have hwcE : w ∈ cE ρ.range := by
    apply hy
    refine ⟨?_, hwE⟩
    show ρ y w - w ∈ cE ρ.range
    rw [hwfix, sub_self]
    exact Submodule.zero_mem _
  rw [← hwc]
  exact Submodule.add_mem _ (cE_le_fixSub ρ.range hwcE) hc

theorem Setting12Two.two_pow_le_card_quotient
    (hMult : SchurMultiplierInput) (h : Setting12Two A M n) (hA : IsElemAbelian 2 A)
    (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) {P Q : Submodule (ZMod 2) V}
    (hPA : P ≤ fixSub (A.map ρ)) (hQP : Q < P) (hP : ∀ m ∈ M, ∀ v ∈ P, ρ m v ∈ P)
    (hQ : ∀ m ∈ M, ∀ v ∈ Q, ρ m v ∈ Q) (hfix : P ⊓ fixSub ρ.range ≤ Q) :
    2 ^ n ≤ Nat.card (↥P ⧸ Submodule.comap P.subtype Q) := by
  classical
  change 2 ^ n ≤ Nat.card (SecMod P Q)
  let K : Subgroup G := CFSG.Quasithin.kerIn M ⊤
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  haveI hKnormal : K.Normal := kerIn_top_normal12 M
  have hKM : K ≤ M := CFSG.Quasithin.kerIn_le
  obtain ⟨C, hCle, hCcard, hClift⟩ := Setting12Two.exists_cartan_lifts h hA ρ hq
  let L : Subgroup G := C.comap π
  have hKL : K ≤ L := by
    intro k hk
    rw [Subgroup.mem_comap]
    have h1 : (k : G ⧸ K) = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [show π k = (k : G ⧸ K) from rfl, h1]
    exact C.one_mem
  have hLM : L ≤ M := by
    intro x hx
    have hπx : π x ∈ C := Subgroup.mem_comap.mp hx
    obtain ⟨m, hmM, hmg⟩ := Subgroup.mem_map.mp (hCle hπx)
    have hkx : m⁻¹ * x ∈ K := by
      have h1 : ((m⁻¹ * x : G) : G ⧸ K) = 1 := by
        change π (m⁻¹ * x) = 1
        rw [map_mul, map_inv, show π m = π x from hmg, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (m⁻¹ * x)).mp h1
    have hxeq : x = m * (m⁻¹ * x) := by group
    rw [hxeq]
    exact M.mul_mem hmM (hKM hkx)
  have hMP : ∀ g : ↥M, ∀ w ∈ P, (ρ.comp M.subtype) g w ∈ P :=
    fun g w hw => hP (g : G) g.2 w hw
  have hMQ : ∀ g : ↥M, ∀ w ∈ Q, (ρ.comp M.subtype) g w ∈ Q :=
    fun g w hw => hQ (g : G) g.2 w hw
  let σ : ↥M →* LGL 2 (SecMod P Q) := sectionRep (ρ.comp M.subtype) P Q hMP hMQ
  have hKmap2 : IsPGroup 2 (K.map ρ) := Setting12Two.isPGroup_map_ker hMult h ρ hq
  have hKP : ∀ g : K.map ρ, ∀ w ∈ P, ((g : LGL 2 V) : V →ₗ[ZMod 2] V) w ∈ P := by
    intro g w hw
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.2
    show (g : LGL 2 V) w ∈ P
    rw [← hkg]
    exact hP k (hKM hk) w hw
  have hKQ : ∀ g : K.map ρ, ∀ w ∈ Q, ((g : LGL 2 V) : V →ₗ[ZMod 2] V) w ∈ Q := by
    intro g w hw
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.2
    show (g : LGL 2 V) w ∈ Q
    rw [← hkg]
    exact hQ k (hKM hk) w hw
  let σK : (K.map ρ) →* LGL 2 (SecMod P Q) := sectionRep (K.map ρ).subtype P Q hKP hKQ
  obtain ⟨-, p, hpP, hpQ⟩ := SetLike.lt_iff_le_and_exists.mp hQP
  have hqne : (Submodule.Quotient.mk (⟨p, hpP⟩ : ↥P) : SecMod P Q) ≠ 0 := by
    intro h
    apply hpQ
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact Submodule.mem_comap.mp h
  have htop_ne_bot : (⊤ : Submodule (ZMod 2) (SecMod P Q)) ≠ ⊥ := by
    intro hbot
    have hmem : (Submodule.Quotient.mk (⟨p, hpP⟩ : ↥P) : SecMod P Q) ∈
        (⊥ : Submodule (ZMod 2) (SecMod P Q)) := by
      rw [← hbot]; exact Submodule.mem_top
    exact hqne (by simpa using hmem)
  haveI : Finite (SecMod P Q) :=
    Finite.of_surjective (Submodule.Quotient.mk : ↥P → SecMod P Q)
      (Submodule.Quotient.mk_surjective _)
  obtain ⟨b, -, hbne, hbfixK⟩ :=
    exists_fixed_vector_of_isPGroup (G := ↥(K.map ρ)) (V := SecMod P Q) σK
      (hKmap2.to_subgroup ⊤) (W := ⊤) (by intro g _ w _; exact Submodule.mem_top)
      htop_ne_bot
  have hbfix_K : ∀ x : ↥L, (x : G) ∈ K → σ (Subgroup.inclusion hLM x) b = b := by
    intro x hxK
    have h1 : σ (Subgroup.inclusion hLM x) =
        σK ⟨ρ (x : G), Subgroup.mem_map_of_mem ρ hxK⟩ := by
      apply LinearEquiv.ext
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H pr =>
        obtain ⟨v, hv⟩ := pr
        rw [sectionRep_mk]
        rfl
    rw [h1]
    exact hbfixK ⟨ρ (x : G), _⟩ (Subgroup.mem_top _)
  have hfpf : ∀ (m : G) (hm : m ∈ M), Odd (orderOf m) →
      fixMod (cE ρ.range) (ρ m) ⊓ commSub ρ.range ≤ cE ρ.range →
      ∀ w : SecMod P Q, σ ⟨m, hm⟩ w = w → w = 0 := by
    intro m hm hodd hfixm w
    induction w using Submodule.Quotient.induction_on with
    | H pr =>
      obtain ⟨p₀, hp₀P⟩ := pr
      intro hw
      have hσp : σ ⟨m, hm⟩ (Submodule.Quotient.mk (⟨p₀, hp₀P⟩ : ↥P)) =
          Submodule.Quotient.mk (⟨ρ m p₀, hMP ⟨m, hm⟩ p₀ hp₀P⟩ : ↥P) :=
        sectionRep_mk (ρ.comp M.subtype) P Q hMP hMQ ⟨m, hm⟩ p₀ hp₀P
      have heq : (Submodule.Quotient.mk (⟨ρ m p₀, hMP ⟨m, hm⟩ p₀ hp₀P⟩ : ↥P) :
            SecMod P Q) = Submodule.Quotient.mk (⟨p₀, hp₀P⟩ : ↥P) := by
        rw [← hσp]; exact hw
      have hdiff : ρ m p₀ - p₀ ∈ Q := by
        have hmem := (Submodule.Quotient.eq (p := Q.comap P.subtype)).mp heq
        rw [Submodule.mem_comap] at hmem
        simpa using hmem
      have hppP : ∀ i : ℕ, ((ρ m) ^ i) p₀ ∈ P := by
        intro i
        induction i with
        | zero => simpa using hp₀P
        | succ i ih =>
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hP m hm _ ih
      let p' : V := ∑ i ∈ Finset.range (orderOf m), ((ρ m) ^ i) p₀
      have hp'P : p' ∈ P := Submodule.sum_mem _ (fun i _ => hppP i)
      have hp'fix : ρ m p' = p' := by
        have h1 : ρ m p' = ∑ i ∈ Finset.range (orderOf m), ((ρ m) ^ (i + 1)) p₀ := by
          simp only [p', map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_succ', LinearEquiv.mul_apply]
        have h2 := Finset.sum_range_succ' (fun i => ((ρ m) ^ i) p₀) (orderOf m)
        have h3 := Finset.sum_range_succ (fun i => ((ρ m) ^ i) p₀) (orderOf m)
        have h4 : ((ρ m) ^ orderOf m) p₀ = ((ρ m) ^ 0) p₀ := by
          have h : (ρ m) ^ orderOf m = 1 :=
            (orderOf_dvd_iff_pow_eq_one).mp (orderOf_map_dvd ρ m)
          rw [h, pow_zero]
        have h5 : ∑ i ∈ Finset.range (orderOf m), ((ρ m) ^ (i + 1)) p₀ + ((ρ m) ^ 0) p₀ =
            ∑ i ∈ Finset.range (orderOf m), ((ρ m) ^ i) p₀ + ((ρ m) ^ orderOf m) p₀ := by
          rw [← h2, ← h3]
        rw [h4] at h5
        rw [h1]
        exact add_right_cancel h5
      have hdiff_pow : ∀ i : ℕ, ((ρ m) ^ i) p₀ - p₀ ∈ Q := by
        intro i
        induction i with
        | zero => simpa using (Q.zero_mem)
        | succ i ih =>
          have hstep : ((ρ m) ^ (i + 1)) p₀ - p₀ =
              ρ m (((ρ m) ^ i) p₀ - p₀) + (ρ m p₀ - p₀) := by
            rw [pow_succ', LinearEquiv.mul_apply, map_sub]
            abel
          rw [hstep]
          exact Q.add_mem (hQ m hm _ ih) hdiff
      have hmu : (orderOf m) • p₀ = p₀ := by
        have h1 : ((orderOf m : ℕ) : ZMod 2) = 1 := hodd.natCast_zmod_two
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2) (orderOf m) p₀, h1, one_smul]
      have hp'Q : p' - p₀ ∈ Q := by
        have hsum : p' - p₀ =
            ∑ i ∈ Finset.range (orderOf m), (((ρ m) ^ i) p₀ - p₀) := by
          rw [show p' = ∑ i ∈ Finset.range (orderOf m), ((ρ m) ^ i) p₀ from rfl,
            Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, hmu]
        rw [hsum]
        exact Submodule.sum_mem _ (fun i _ => hdiff_pow i)
      have hp'mk : (Submodule.Quotient.mk (⟨p', hp'P⟩ : ↥P) : SecMod P Q) =
          Submodule.Quotient.mk (⟨p₀, hp₀P⟩ : ↥P) := by
        rw [Submodule.Quotient.eq]
        exact Submodule.mem_comap.mpr (by simpa using hp'Q)
      have hp'G : p' ∈ fixSub ρ.range :=
        Setting12Two.mem_fixSub_range_of_fix h hA ρ hq hfixm (hPA hp'P) hp'fix
      have hp'Q' : p' ∈ Q := hfix ⟨hp'P, hp'G⟩
      rw [← hp'mk, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr (by simpa using hp'Q')
  have hLs : ∀ δ : ↥C, ∃ x : ↥L, π (x : G) = (δ : G ⧸ K) := by
    intro δ
    obtain ⟨m, hmM, hmg⟩ := Subgroup.mem_map.mp (hCle δ.2)
    exact ⟨⟨m, Subgroup.mem_comap.mpr (by rw [hmg]; exact δ.2)⟩, hmg⟩
  let s : ↥C → ↥L := fun δ => Classical.choose (hLs δ)
  have hs : ∀ δ : ↥C, π (s δ : G) = (δ : G ⧸ K) := fun δ => Classical.choose_spec (hLs δ)
  let F : ↥C → {w : SecMod P Q // w ≠ 0} := fun δ =>
    ⟨σ (Subgroup.inclusion hLM (s δ)) b, by
      intro h
      apply hbne
      have h2 : σ (Subgroup.inclusion hLM (s δ)) b = 0 := h
      calc b = (σ (Subgroup.inclusion hLM (s δ))).symm
            (σ (Subgroup.inclusion hLM (s δ)) b) :=
            ((σ (Subgroup.inclusion hLM (s δ))).symm_apply_apply b).symm
        _ = (σ (Subgroup.inclusion hLM (s δ))).symm 0 := by rw [h2]
        _ = 0 := map_zero _⟩
  have hF_inj : Function.Injective F := by
    intro δ δ' hFF
    have hb_eq : σ (Subgroup.inclusion hLM (s δ)) b =
        σ (Subgroup.inclusion hLM (s δ')) b := congrArg Subtype.val hFF
    set x : ↥L := (s δ)⁻¹ * (s δ') with hxdef
    have hxfix : σ (Subgroup.inclusion hLM x) b = b := by
      have h1 : Subgroup.inclusion hLM x =
          (Subgroup.inclusion hLM (s δ))⁻¹ * Subgroup.inclusion hLM (s δ') := by
        rw [hxdef, map_mul, map_inv]
      rw [h1, map_mul, map_inv, LinearEquiv.mul_apply, ← hb_eq]
      exact (σ (Subgroup.inclusion hLM (s δ))).symm_apply_apply b
    have hπx : π (x : G) = ((δ⁻¹ * δ' : ↥C) : G ⧸ K) := by
      have hcoe : (x : G) = (s δ : G)⁻¹ * (s δ' : G) := by rw [hxdef]; rfl
      rw [hcoe, map_mul, map_inv, hs δ, hs δ']
      rfl
    by_cases hδ : δ⁻¹ * δ' = 1
    · have hx1 : π (x : G) = 1 := by
        rw [hπx]
        simpa using congrArg Subtype.val hδ
      have hxeq : (s δ' : ↥L) = s δ * x := by rw [hxdef]; group
      have hδδ' : (δ : G ⧸ K) = (δ' : G ⧸ K) := by
        have hcoe : ((s δ' : ↥L) : G) = (s δ : G) * (x : G) := by rw [hxeq]; rfl
        rw [← hs δ', hcoe, map_mul, hs δ, hx1, mul_one]
      exact Subtype.ext hδδ'
    · exfalso
      have hδ₀ : ((δ⁻¹ * δ' : ↥C) : G ⧸ K) ≠ 1 := fun h => hδ (Subtype.ext h)
      obtain ⟨y, hyM, hyodd, hyπ, hyfixy⟩ :=
        hClift ((δ⁻¹ * δ' : ↥C) : G ⧸ K) (δ⁻¹ * δ').2 hδ₀
      have hyL : y ∈ L := Subgroup.mem_comap.mpr (by rw [hyπ]; exact (δ⁻¹ * δ').2)
      have hmemK : (⟨y, hyL⟩ : ↥L)⁻¹ * x ∈ K.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        apply (QuotientGroup.eq_one_iff (((⟨y, hyL⟩ : ↥L)⁻¹ * x : ↥L) : G)).mp
        change π (((⟨y, hyL⟩ : ↥L)⁻¹ * x : ↥L) : G) = 1
        have hcoe : (((⟨y, hyL⟩ : ↥L)⁻¹ * x : ↥L) : G) =
            ((⟨y, hyL⟩ : ↥L) : G)⁻¹ * (x : G) := rfl
        rw [hcoe, map_mul, map_inv, hyπ, hπx, inv_mul_cancel]
      have hfixk : σ (Subgroup.inclusion hLM ((⟨y, hyL⟩ : ↥L)⁻¹ * x)) b = b :=
        hbfix_K _ (Subgroup.mem_subgroupOf.mp hmemK)
      have hyb : σ (Subgroup.inclusion hLM ⟨y, hyL⟩) b = b := by
        have h2 : Subgroup.inclusion hLM x =
            Subgroup.inclusion hLM ⟨y, hyL⟩ *
              Subgroup.inclusion hLM ((⟨y, hyL⟩ : ↥L)⁻¹ * x) := by
          rw [← map_mul]
          congr 1
          group
        rw [h2, map_mul, LinearEquiv.mul_apply, hfixk] at hxfix
        exact hxfix
      have hybM : σ ⟨y, hyM⟩ b = b := by
        have h3 : Subgroup.inclusion hLM ⟨y, hyL⟩ = ⟨y, hyM⟩ := Subtype.ext rfl
        rwa [h3] at hyb
      exact hbne (hfpf y hyM hyodd hyfixy b hybM)
  have hle : Nat.card ↥C ≤ Nat.card {w : SecMod P Q // w ≠ 0} :=
    Nat.card_le_card_of_injective F hF_inj
  have hcard_ne : Nat.card {w : SecMod P Q // w ≠ 0} + 1 = Nat.card (SecMod P Q) := by
    haveI : Fintype (SecMod P Q) := Fintype.ofFinite _
    haveI : Fintype {w : SecMod P Q // w ≠ 0} := Fintype.ofFinite _
    have h : Fintype.card {w : SecMod P Q // w ≠ 0} = Fintype.card (SecMod P Q) - 1 := by
      rw [Fintype.card_subtype_compl (p := fun w : SecMod P Q => w = 0),
        Fintype.card_subtype_eq (0 : SecMod P Q)]
    rw [Nat.card_eq_fintype_card (α := {w : SecMod P Q // w ≠ 0}), h, Nat.card_eq_fintype_card]
    have hpos : 1 ≤ Fintype.card (SecMod P Q) := Fintype.card_pos_iff.mpr ⟨0⟩
    omega
  have h1 : Nat.card ↥C + 1 ≤ Nat.card (SecMod P Q) := by
    calc Nat.card ↥C + 1 ≤ Nat.card {w : SecMod P Q // w ≠ 0} + 1 :=
          Nat.add_le_add_right hle 1
      _ = Nat.card (SecMod P Q) := hcard_ne
  rw [hCcard] at h1
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
