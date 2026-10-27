module

public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4_normalizes_J {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagOn Bs L) :
    Bs ≤ Subgroup.normalizer (J : Set G) := by
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hJeq : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.1
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_mono
      (P' := fun _ _ _ _ _ _ => Bs ≤ Subgroup.normalizer (L : Set G))
      (fun _ _ _ _ _ _ hp => hp.1) hInn
    obtain ⟨R, _, I, F, -, -, θ, hP'⟩ := largeEvenRawDatum_exists hraw
    exact hP'
  have hBsD : Bs ≤ Subgroup.centralizer (D : Set G) :=
    (GGBstar.le_centralizer hcfg.2.1).trans (Subgroup.centralizer_le hDB)
  rw [hJeq]
  exact le_normalizer_of_map_conj_le fun g hg =>
    map_conj_largeEvenLayer_le (mem_normalizer_inf_centralizer (hBsL hg) (hBsD hg))

private theorem r4f_log_card_bs {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') (hspan : Submodule.span (ZMod p) (Set.range h') = ⊤)
    (hcard : Fintype.card Λ = 4) :
    Nat.log p (Nat.card Bs) = 5 := by
  have hb : Module.Basis (Option Λ) (ZMod p) V :=
    Module.Basis.mk hD.indep (le_of_eq hspan.symm)
  have hdim : Module.finrank (ZMod p) V = 5 := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_option, hcard]
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = p ^ 5 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := V), hdim,
      ZMod.card]
  have hcardBsV : Nat.card Bs = Nat.card V :=
    (Nat.card_congr (Additive.ofMul : ↥Bs ≃ Additive ↥Bs)).trans
      (Nat.card_congr ι.toEquiv)
  rw [hcardBsV, hcardV]
  exact Nat.log_pow (Fact.out : p.Prime).one_lt 5

private theorem r4f_pow_three_le_card_inf {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    [Fact (Nat.Prime 3)]
    (hD : GGExtDatum ι X φ' h' α') (hcard : Fintype.card Λ = 4) {b : Λ}
    (hNJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hJ : ∀ j : Λ, j ≠ b → φ' (some j) ∈ ggAutomizer J Bs) :
    3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by
  classical
  let S := {j : Λ // j ≠ b}
  have hcardS : Fintype.card S = 3 := by
    have h := Fintype.card_subtype_compl (fun j : Λ => j = b)
    have hb1 : Fintype.card {j : Λ // j = b} = 1 := Fintype.card_subtype_eq b
    rw [hb1, hcard] at h
    rw [show (4 : ℕ) - 1 = 3 from rfl] at h
    simpa [S] using h
  let g := (Fintype.equivFinOfCardEq hcardS).symm
  choose n hnJ hnN hnconj using fun j : S => mem_ggAutomizer_iff.mp (hJ j.1 j.2)
  let a : S → ↥Bs := fun j => Additive.toMul (ι.symm (h' (some j.1)))
  have hιa : ∀ j : S, ι (Additive.ofMul (a j)) = h' (some j.1) := by
    intro j
    simp [a]
  have hφa : ∀ j : S, φ' (some j.1) (a j) = (a j)⁻¹ := by
    intro j
    have h1 : ι (Additive.ofMul (φ' (some j.1) (a j))) = - h' (some j.1) := by
      rw [← ggLin_apply_ofMul (p := 3), hιa j, hD.lin (some j.1) (h' (some j.1)),
        hD.pair (some j.1) (some j.1), hD.diag (some j.1)]
      module
    have h2 : ι (Additive.ofMul ((a j)⁻¹)) = - h' (some j.1) := by
      rw [ofMul_inv, map_neg, hιa j]
    exact Additive.ofMul.injective (ι.injective (h1.trans h2.symm))
  have hconj : ∀ j : S, n j * (a j : G) * (n j)⁻¹ = (((a j)⁻¹ : ↥Bs) : G) := by
    intro j
    have := hnconj j (a j)
    rw [hφa j] at this
    exact this.symm
  let d : S → ↥Bs := fun j => ⟨n j * (a j : G) * (n j)⁻¹,
    (show n j * (a j : G) * (n j)⁻¹ ∈ Bs by rw [hconj j]; exact (a j)⁻¹ |>.2)⟩
  have hd_eq : ∀ j : S, d j = (a j)⁻¹ := fun j => Subtype.ext (hconj j)
  let c : S → ↥Bs := fun j => d j * (a j)⁻¹
  have hcJ : ∀ j : S, ((c j : ↥Bs) : G) ∈ J := by
    intro j
    have h2 : (a j : G) * (n j)⁻¹ * (a j : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hNJ (a j).2) ((n j)⁻¹)).mp (J.inv_mem (hnJ j))
    have h1 : (n j * (a j : G) * (n j)⁻¹ * (a j : G)⁻¹) ∈ J := by
      have := J.mul_mem (hnJ j) h2
      simpa [mul_assoc] using this
    simpa [c, d] using h1
  have hιc : ∀ j : S, ι (Additive.ofMul (c j)) = (-2 : ZMod 3) • h' (some j.1) := by
    intro j
    have hd : ι (Additive.ofMul (d j)) = - h' (some j.1) := by
      rw [hd_eq j, ofMul_inv, map_neg, hιa j]
    have ha : ι (Additive.ofMul ((a j)⁻¹)) = - h' (some j.1) := by
      rw [ofMul_inv, map_neg, hιa j]
    have hmul : Additive.ofMul (c j) = Additive.ofMul (d j) + Additive.ofMul ((a j)⁻¹) := by
      dsimp only [c]
      rw [ofMul_mul]
    rw [hmul, map_add, hd, ha, ← neg_add, ← two_smul (ZMod 3) (h' (some j.1))]
    exact (neg_smul (2 : ZMod 3) (h' (some j.1))).symm
  have hc3 : ∀ j : S, (c j) ^ 3 = 1 := by
    intro j
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, map_nsmul, hιc j, ofMul_one, map_zero]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3 ((-2 : ZMod 3) • h' (some j.1)), ← mul_smul,
      ZMod.natCast_self 3, zero_mul, zero_smul]
  let cc : S → ↥(Bs ⊓ J) := fun j =>
    ⟨(c j : G), Subgroup.mem_inf.mpr ⟨(c j).2, hcJ j⟩⟩
  let f : (Fin 3 → ZMod 3) → ↥(Bs ⊓ J) := fun k =>
    (cc (g 0)) ^ (k 0).val * (cc (g 1)) ^ (k 1).val * (cc (g 2)) ^ (k 2).val
  have hincl : ∀ k, Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f k) =
      (c (g 0)) ^ (k 0).val * (c (g 1)) ^ (k 1).val * (c (g 2)) ^ (k 2).val := by
    intro k
    simp only [f, cc, map_mul, map_pow]
    rfl
  have hformula : ∀ k, ι (Additive.ofMul (Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left)
      (f k))) = ∑ i : Fin 3, ((-2 : ZMod 3) * k i) • h' (some (g i).1) := by
    intro k
    rw [hincl k, Fin.sum_univ_three]
    rw [ofMul_mul, ofMul_mul, ofMul_pow, ofMul_pow, ofMul_pow, map_add, map_add, map_nsmul,
      map_nsmul, map_nsmul, hιc, hιc, hιc]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) (k 0).val ((-2 : ZMod 3) • h' (some (g 0).1)),
      ← Nat.cast_smul_eq_nsmul (ZMod 3) (k 1).val ((-2 : ZMod 3) • h' (some (g 1).1)),
      ← Nat.cast_smul_eq_nsmul (ZMod 3) (k 2).val ((-2 : ZMod 3) • h' (some (g 2).1)),
      ZMod.natCast_zmod_val (k 0), ZMod.natCast_zmod_val (k 1), ZMod.natCast_zmod_val (k 2)]
    module
  have hf_inj : Function.Injective f := by
    intro k l hkl
    have h1 : Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f k) =
        Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f l) := by rw [hkl]
    have h2 : ι (Additive.ofMul (Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f k))) =
        ι (Additive.ofMul (Subgroup.inclusion (show Bs ⊓ J ≤ Bs from inf_le_left) (f l))) := by
      rw [h1]
    rw [hformula k, hformula l] at h2
    have h3 : ∑ i : Fin 3,
        (((-2 : ZMod 3) * k i) - ((-2 : ZMod 3) * l i)) • h' (some (g i).1) = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib, h2, sub_self]
    have hind : LinearIndependent (ZMod 3) (fun i : Fin 3 => h' (some (g i).1)) :=
      hD.indep.comp (fun i : Fin 3 => some (g i).1)
        (fun i j hij => g.injective (Subtype.ext (Option.some_injective Λ hij)))
    have hcoef := fun i => (Fintype.linearIndependent_iff.mp hind
      (fun i => ((-2 : ZMod 3) * k i) - ((-2 : ZMod 3) * l i)) h3 i)
    funext i
    have h4 : (-2 : ZMod 3) * (k i - l i) = 0 := by
      rw [mul_sub]; exact hcoef i
    have h4' : k i - l i = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exfalso
        have h2ne : (2 : ZMod 3) ≠ 0 := by
          intro hzero
          have hval : ((2 : ZMod 3)).val = 0 := by rw [hzero]; rfl
          have h2 : ((2 : ZMod 3)).val = 2 := ZMod.val_cast_of_lt (by norm_num : 2 < 3)
          omega
        exact h2ne (neg_eq_zero.mp h)
      · exact h
    exact sub_eq_zero.mp h4'
  have hle := Nat.card_le_card_of_injective f hf_inj
  have hdom : Nat.card (Fin 3 → ZMod 3) = 3 ^ 3 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rwa [hdom] at hle

private theorem r4f_mem_center_of_mem_center_quotient {Q : Type} [Group Q]
    (hq : CFSG.Assembly.IsQuasisimple Q) {N : Subgroup Q} [N.Normal]
    (hN : N ≤ Subgroup.center Q) {z : Q ⧸ N} (hz : z ∈ Subgroup.center (Q ⧸ N)) :
    ∃ g ∈ Subgroup.center Q, (g : Q ⧸ N) = z := by
  have : Group.IsPerfect Q := Group.isPerfect_def.mpr hq.1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
  refine ⟨g, ?_, rfl⟩
  have hgz : (QuotientGroup.mk' (Subgroup.center Q)) g ∈
      Subgroup.center (Q ⧸ Subgroup.center Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) y
    rw [← map_mul, ← map_mul]
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have hcomm : (QuotientGroup.mk' N) (h * g) = (QuotientGroup.mk' N) (g * h) := by
      have hc := (Subgroup.mem_center_iff.mp hz) (QuotientGroup.mk' N h)
      rwa [← map_mul, ← map_mul] at hc
    have hcomm' : ((h * g : Q) : Q ⧸ N) = ((g * h : Q) : Q ⧸ N) := by
      simpa only [QuotientGroup.mk'_apply] using hcomm
    exact hN (QuotientGroup.eq.mp hcomm')
  rw [Group.IsPerfect.center_quotient_center_eq_bot Q] at hgz
  rw [Subgroup.mem_bot] at hgz
  rw [← QuotientGroup.ker_mk' (Subgroup.center Q), MonoidHom.mem_ker]
  exact hgz

private theorem r4f_OmegaOneCenter_eq_bot {G : Type} [Group G] [Finite G]
    {J : Subgroup G} [Fact (Nat.Prime 3)]
    (hJ : 3 ∣ Nat.card ↥J) (hqs : CFSG.Assembly.IsQuasisimple J)
    (hZ2 : ∀ g ∈ Subgroup.center ↥J, ∃ k : ℕ, orderOf g = 2 ^ k) :
    ggOmegaOneCenter 3 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := Subgroup.center ↥J
  let N := LargeEvenPPrimeCore 3 ↥J
  have hNZ : N ≤ Z := by
    have : IsSimpleGroup (↥J ⧸ Z) := hqs.2
    have hNnorm : (N.map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
    rcases Subgroup.Normal.eq_bot_or_eq_top (N.map (QuotientGroup.mk' Z)) with hbot | htop
    · have hle : N ≤ (QuotientGroup.mk' Z).ker := (Subgroup.map_eq_bot_iff N).mp hbot
      rwa [QuotientGroup.ker_mk'] at hle
    · exfalso
      have hsup : N ⊔ Z = ⊤ := by
        have h := congrArg (Subgroup.comap (QuotientGroup.mk' Z)) htop
        simpa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using h
      have hc := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute N Z
        (fun x _ y hy => Subgroup.mem_center_iff.mp hy x)
      rw [hsup, Subgroup.card_top] at hc
      have hNcop : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
      have h3N : ¬ 3 ∣ Nat.card N :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hNcop
      have hZpg : IsPGroup 2 Z := fun g => by
        obtain ⟨k, hk⟩ := hZ2 g g.2
        exact ⟨k, by rw [← hk, Subgroup.orderOf_coe]; exact pow_orderOf_eq_one g⟩
      have h3Z : ¬ 3 ∣ Nat.card Z := by
        obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hZpg
        rw [hk]
        intro h3
        exact (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)
      have h3prod : 3 ∣ Nat.card N * Nat.card Z := by
        rw [← hc.1]
        exact dvd_mul_of_dvd_left hJ _
      rcases (Nat.prime_three.dvd_mul).mp h3prod with h | h
      · exact h3N h
      · exact h3Z h
  have hcenter : Subgroup.center (↥J ⧸ N) = Z.map (QuotientGroup.mk' N) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨g, hg, hgz⟩ := r4f_mem_center_of_mem_center_quotient hqs hNZ hz
      exact Subgroup.mem_map.mpr ⟨g, hg, by rw [QuotientGroup.mk'_apply]; exact hgz⟩
    · rintro z ⟨g, hg, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg h]
  have hZpg : IsPGroup 2 Z := fun g => by
    obtain ⟨k, hk⟩ := hZ2 g g.2
    exact ⟨k, by rw [← hk, Subgroup.orderOf_coe]; exact pow_orderOf_eq_one g⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hZpg
  have hcop : Nat.Coprime 3 (Nat.card (Z.map (QuotientGroup.mk' N))) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have hdvd : Nat.card (Z.map (QuotientGroup.mk' N)) ∣ 2 ^ k :=
      (Subgroup.card_map_dvd Z (QuotientGroup.mk' N)).trans (by rw [hk])
    exact (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow (h3.trans hdvd))
  rw [ggOmegaOneCenter_eq_bot_of_coprime]
  rw [hcenter]
  exact hcop

theorem ggR4_rank {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {Bs J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') (hspan : Submodule.span (ZMod p) (Set.range h') = ⊤)
    (hcard : Fintype.card Λ = 4) {b : Λ} (hNJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hJ : ∀ j : Λ, j ≠ b → φ' (some j) ∈ ggAutomizer J Bs)
    (hqs : CFSG.Assembly.IsQuasisimple J)
    (hZ2 : ∀ g ∈ Subgroup.center ↥J, ∃ k : ℕ, orderOf g = 2 ^ k) :
    Nat.log p (Nat.card Bs) + Nat.log p (Nat.card (ggOmegaOneCenter p J)) <
      2 * Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)) := by
  subst hp3
  have hlogBs : Nat.log 3 (Nat.card Bs) = 5 := r4f_log_card_bs (p := 3) hD hspan hcard
  have hbound : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
    r4f_pow_three_le_card_inf hD hcard hNJ hJ
  have hlogJ : 3 ≤ Nat.log 3 (Nat.card (Bs ⊓ J : Subgroup G)) :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 3) hbound
  have hBs3 : ∀ x : ↥Bs, x ^ 3 = 1 := by
    intro x
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, map_nsmul, ofMul_one, map_zero,
      ← Nat.cast_smul_eq_nsmul (ZMod 3) 3 (ι (Additive.ofMul x)), ZMod.natCast_self 3,
      zero_smul]
  have hpow : IsPGroup 3 (Bs ⊓ J : Subgroup G) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show ((g : G) ^ 3) = 1
    have h := hBs3 ⟨(g : G), g.2.1⟩
    simpa using congrArg Subtype.val h
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hpow
  have h3le : 3 ≤ k := by
    have h := hbound
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have h3div : 3 ∣ Nat.card (Bs ⊓ J : Subgroup G) := by
    rw [hk]
    exact dvd_pow_self 3 (by omega)
  have hcard_eq : Nat.card ↥((Bs ⊓ J).subgroupOf J) = Nat.card ↥(Bs ⊓ J : Subgroup G) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.2⟩
        invFun := fun x => ⟨⟨(x.1 : G), (inf_le_right : (Bs ⊓ J : Subgroup G) ≤ J) x.2⟩, x.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun x => by ext; rfl }
  have h3J : 3 ∣ Nat.card ↥J :=
    h3div.trans (hcard_eq ▸ Subgroup.card_subgroup_dvd_card ((Bs ⊓ J).subgroupOf J))
  have hOmega : ggOmegaOneCenter 3 J = ⊥ := r4f_OmegaOneCenter_eq_bot h3J hqs hZ2
  have hlogOmega : Nat.log 3 (Nat.card (ggOmegaOneCenter 3 J)) = 0 := by
    rw [hOmega, Subgroup.card_bot, Nat.log_one_right]
  rw [hlogBs, hlogOmega]
  omega

theorem ggR4_five_dvd {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {z : G} (hz : z ∈ Bs) (hE : IsElemAbelian p Bs)
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X) (hJX : J ≤ X)
    (hrank : Nat.log p (Nat.card Bs) + Nat.log p (Nat.card (ggOmegaOneCenter p J)) <
      2 * Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)))
    {ρ : MulAut ↥Bs} (hρ : ρ ∈ ggAutomizer ⊤ Bs) (hρz : ρ ⟨z, hz⟩ = ⟨z, hz⟩)
    {s : Fin 4 → MulAut ↥Bs} (hs : ∀ i, s i ∈ ggAutomizer J Bs)
    (h5 : 5 ∣ orderOf (s 0 * s 1 * s 2 * (ρ * s 3 * ρ⁻¹))) :
    5 ∣ Nat.card (ggAutomizer X Bs) := by
  let g : MulAut ↥Bs := s 0 * s 1 * s 2 * (ρ * s 3 * ρ⁻¹)
  have hg5 : 5 ∣ orderOf g := by simpa [g] using h5
  have hN : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (X : Set G) :=
    normalizer_inf_le_normalizer_of_pComponent_of_rank
      (H := Subgroup.centralizer ({z} : Set G)) hX hJX hE hrank
  have hR : ∀ r ∈ ({ρ} : Set (MulAut ↥Bs)),
      r ∈ ggAutomizer ⊤ Bs ∧ r ⟨z, hz⟩ = ⟨z, hz⟩ := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hρ, hρz⟩
  have hS : ({s 3} : Set (MulAut ↥Bs)) ⊆ (ggAutomizer J Bs : Set (MulAut ↥Bs)) := by
    intro φ hφ
    rw [Set.mem_singleton_iff] at hφ
    subst hφ
    exact hs 3
  have horb := ggAutomizer_orbit_le_of_normalizer_le hz hX.1 hJX hN hR hS
  have hρs3 : ρ * s 3 * ρ⁻¹ ∈ ggAutomizer X Bs :=
    horb.1 ⟨ρ, Subgroup.subset_closure (Set.mem_singleton ρ), s 3, rfl, rfl⟩
  have hsX : ∀ i : Fin 4, s i ∈ ggAutomizer X Bs := fun i => ggAutomizer_mono Bs hJX (hs i)
  have hgmem : g ∈ ggAutomizer X Bs := by
    simp only [g]
    exact mul_mem (mul_mem (mul_mem (hsX 0) (hsX 1)) (hsX 2)) hρs3
  exact hg5.trans (Subgroup.orderOf_dvd_natCard (ggAutomizer X Bs) hgmem)

end CFSG.StandardType
