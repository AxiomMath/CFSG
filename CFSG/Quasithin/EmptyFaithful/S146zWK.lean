module

public import CFSG.Quasithin.EmptyFaithful.S146zWJ
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.SBc17

section Out5

theorem out5Inner_of_card_sixty {L : Type*} [Group L] [Finite L]
    [IsSimpleGroup L] (h : Nat.card L = 60) : Out5Inner L := by
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h
  exact Out5Inner.of_mulEquiv e.symm (out5Inner_alternating (by norm_num))

theorem out5Inner_GL32 : Out5Inner (CFSG.QuasithinUnique.Setup.Family.GL32) := by
  apply out5Inner_of_card_mulAut_le CFSG.QuasithinUnique.Setup.Family.center_GL32
  rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32,
    CFSG.LieType.SteinbergBR.AutGL32.card_GL32]
  norm_num

noncomputable def statedSL_three_equiv_GL32 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ↥(StatedSL 3 F) ≃* CFSG.QuasithinUnique.Setup.Family.GL32 := by
  have hfin : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let r : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hcard
  let m : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin 3) F :=
    Matrix.SpecialLinearGroup.map (r : ZMod 2 →+* F)
  have hinj : Function.Injective m := by
    intro A B h
    ext i j
    have := congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) i j) h
    simpa [m] using r.injective this
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rw [Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
      Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv, card_statedSL_three,
      card_statedSL_three, hF, Nat.card_zmod]
  have hbij : Function.Bijective m :=
    hinj.bijective_of_nat_card_le hcardSL.le
  exact (specialLinearGroupEquivStatedSL 3 F).symm.trans
    ((MulEquiv.ofBijective m hbij).symm.trans
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3))

theorem out5Inner_of_statedSL_three_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {L : Type*} [Group L] (e : L ≃* ↥(StatedSL 3 F)) : Out5Inner L :=
  Out5Inner.of_mulEquiv (e.trans (statedSL_three_equiv_GL32 hF)).symm out5Inner_GL32

theorem out5Inner_of_swType {Ω : Type} [Group Ω] [Finite Ω]
    {L : Subgroup Ω} (h : SwType L) (hc : Nat.card ↥L < 504) : Out5Inner ↥L := by
  obtain ⟨hs, h⟩ := h
  have : IsSimpleGroup ↥L := hs
  rcases h with ⟨F, _, _, n, hn, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨F, _, _, m, hm, hmo, hF, ⟨e⟩⟩
  · have hcard : Nat.card ↥L = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, S146zU.UC2.card_statedSL_two]
    have hn2 : n = 2 := by
      by_contra hne
      have h3 : 3 ≤ n := by omega
      have h8 : 8 ≤ Nat.card F := by
        rw [hF]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      have : 8 * (8 ^ 2 - 1) ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
        Nat.mul_le_mul h8 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h8 2) 1)
      omega
    subst hn2
    have h60 : Nat.card ↥L = 60 := by rw [hcard, hF]; norm_num
    exact out5Inner_of_card_sixty h60
  · exact Out5Inner.of_mulEquiv e.symm (out5Inner_alternating (n := 5) le_rfl)
  · have hcard : Nat.card ↥L =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three]
    have hm1 : m = 1 := by
      by_contra hne
      have h2 : 2 ≤ m := by omega
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2
      have h64 : 4 ^ 3 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left h4 3
      have h15 : 4 ^ 2 - 1 ≤ Nat.card F ^ 2 - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 2) 1
      have h63 : 4 ^ 3 - 1 ≤ Nat.card F ^ 3 - 1 := Nat.sub_le_sub_right h64 1
      have : 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) ≤
          Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
        Nat.mul_le_mul h64 (Nat.mul_le_mul h15 h63)
      omega
    subst hm1
    have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
    exact out5Inner_of_statedSL_three_two hF2 e

end Out5

section Central

variable {Γ : Type*} [Group Γ]

theorem out5Inner_of_center_quot (hperf : Group.IsPerfect Γ)
    (h : Out5Inner (Γ ⧸ Subgroup.center Γ)) : Out5Inner Γ := by
  intro φ hφ
  have hmap := Subgroup.map_center_eq φ
  let φ' : MulAut (Γ ⧸ Subgroup.center Γ) := QuotientGroup.congr _ _ φ hmap
  have hφ'x : ∀ x : Γ, φ' (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := fun x => rfl
  have hpow : ∀ (n : ℕ) (x : Γ),
      (φ' ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((φ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ'x, ih]
  have hφ'5 : φ' ^ 5 = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hpow, hφ]
    rfl
  obtain ⟨s, hs⟩ := h φ' hφ'5
  obtain ⟨s₀, rfl⟩ := QuotientGroup.mk_surjective s
  have hdelta : ∀ x : Γ, φ x * (MulAut.conj s₀ x)⁻¹ ∈ Subgroup.center Γ := by
    intro x
    have h1 : (QuotientGroup.mk (φ x) : Γ ⧸ Subgroup.center Γ) =
        QuotientGroup.mk (s₀ * x * s₀⁻¹) := by
      have := hs (QuotientGroup.mk x)
      rw [hφ'x] at this
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
    have h3 : (φ x)⁻¹ * (s₀ * x * s₀⁻¹) ∈ Subgroup.center Γ := QuotientGroup.eq.mp h1
    have h4 := (Subgroup.center Γ).inv_mem h3
    have h5 := (inferInstance : (Subgroup.center Γ).Normal).conj_mem _ h4 (φ x)
    have e : φ x * ((φ x)⁻¹ * (s₀ * x * s₀⁻¹))⁻¹ * (φ x)⁻¹ = φ x * (MulAut.conj s₀ x)⁻¹ := by
      simp only [MulAut.conj_apply]
      group
    rwa [e] at h5
  have hα := CFSG.GorensteinWalter.perfect_central_automorphism_eq hperf φ (MulAut.conj s₀) hdelta
  exact ⟨s₀, fun x => by rw [hα]; rfl⟩

end Central

section Assembly

variable {G : Type} [Group G] [Finite G]

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem out5Inner_of_small (h56 : AsB56) (hA21 : AsA21SQTKSection)
    (hsmall : Nat.card ((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) < 504) :
    Out5Inner (↥J ⧸ CFSG.pCore 2 ↥J) := by
  have hT := d.swType h56 hA21
  obtain ⟨hq₁, -, -, -, -, -, -⟩ := d.moduleFacts
  set Js := wAut J J' R J with hJs
  obtain ⟨f, hf⟩ : ∃ f : ↥J →* ↥Js, Function.Surjective f :=
    exists_surj_wAut (J := J) (J' := J') (R := R) J (J_le_wY J J' R)
  have hsimple : IsSimpleGroup ↥Js := hT.1
  have hJsp : Group.IsPerfect ↥Js := hq₁.1
  have hJsn : Nontrivial ↥Js := CFSG.LocalCores.isQuasisimple_nontrivial hq₁
  have hnotsolv : ¬ Group.IsSolvable ↥Js := Group.IsPerfect.not_isSolvable _
  have hZ : Subgroup.center ↥Js = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Js) with h | h
    · exact h
    · exfalso
      have hab : ∀ a b : ↥Js, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
      exact hnotsolv (Group.isSolvable_of_comm hab)
  have hker : CFSG.pCore 2 ↥J ≤ f.ker := by
    have hnorm : ((CFSG.pCore 2 ↥J).map f).Normal :=
      Subgroup.Normal.map inferInstance f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥J).map f) with h | h
    · intro x hx
      have : f x ∈ (CFSG.pCore 2 ↥J).map f := Subgroup.mem_map_of_mem f hx
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hP : IsPGroup 2 ↥Js := by
        have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).map f
        intro y
        have hy : (y : ↥Js) ∈ (CFSG.pCore 2 ↥J).map f := h ▸ Subgroup.mem_top y
        obtain ⟨k, hk⟩ := h2 ⟨y, hy⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hsolv : Group.IsSolvable ↥Js := by
        have := hP.isNilpotent
        infer_instance
      exact hnotsolv hsolv
  let g : (↥J ⧸ CFSG.pCore 2 ↥J) →* ↥Js := QuotientGroup.lift (CFSG.pCore 2 ↥J) f hker
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hkerg : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = g.ker := by
    apply le_antisymm
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hgz : g z ∈ Subgroup.center ↥Js := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨w, rfl⟩ := hg y
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz w)]
      rw [hZ, Subgroup.mem_bot] at hgz
      exact hgz
    · have hne : g.ker ≠ ⊤ := by
        intro htop
        obtain ⟨a, b, hab⟩ : ∃ a b : ↥Js, a ≠ b := exists_pair_ne _
        obtain ⟨a', rfl⟩ := hg a
        obtain ⟨b', rfl⟩ := hg b
        apply hab
        have h1 : a' ∈ g.ker := htop ▸ Subgroup.mem_top a'
        have h2 : b' ∈ g.ker := htop ▸ Subgroup.mem_top b'
        rw [MonoidHom.mem_ker] at h1 h2
        rw [h1, h2]
      exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
        (B1Red.isQuasisimple_to_open d.cfg.quasi) g.ker hne
  let e : ((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ≃* ↥Js :=
    (QuotientGroup.quotientMulEquivOfEq hkerg).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have hc : Nat.card ↥Js < 504 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hsmall
  have hOut : Out5Inner ↥Js := out5Inner_of_swType hT hc
  exact out5Inner_of_center_quot d.cfg.quasi.1 (Out5Inner.of_mulEquiv e.symm hOut)

end WreathData

end Assembly

end CFSG.Quasithin.S146zW
