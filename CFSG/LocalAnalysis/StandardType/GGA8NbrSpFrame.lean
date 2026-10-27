module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpComp
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrInner
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallASpLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.Open CFSG.StandardType
open CFSG.LieType.Universal

private theorem a8jf_card_units : Nat.card (GaloisField 2 3)ˣ = 7 := by
  rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]
  norm_num

private theorem a8jf_units_pow_seven (u : (GaloisField 2 3)ˣ) : u ^ 7 = 1 := by
  have h := orderOf_dvd_natCard u
  rw [a8jf_card_units] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

private theorem a8jf_exists_zeta_pow {ζ : (GaloisField 2 3)ˣ} (hζ : ζ ^ 7 = 1)
    (hζo : orderOf ζ = 7) (u : (GaloisField 2 3)ˣ) : ∃ k : ZMod 7, ζ ^ k.val = u := by
  have hprim : IsPrimitiveRoot (ζ : GaloisField 2 3) 7 :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζo ▸ IsPrimitiveRoot.orderOf ζ)
  have hui : (u : GaloisField 2 3) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, a8jf_units_pow_seven u, Units.val_one]
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hui
  have hζ' : (ζ : GaloisField 2 3) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  refine ⟨(k : ZMod 7), ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  rw [← hk, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ']

private theorem a8jf_pow_val_add {M : Type*} [Monoid M] {x : M} (hx : x ^ 7 = 1)
    (a b : ZMod 7) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hx]

private theorem a8jf_exists_nat_pow {G : Type*} [Group G] {x : G} (hord : orderOf x = 7)
    {c : G} (hc : c ∈ Subgroup.zpowers x) : ∃ k : ℕ, x ^ k = c := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  refine ⟨(n % 7).toNat, ?_⟩
  rw [← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num : (7 : ℤ) ≠ 0))]
  have h1 : x ^ (n % (7 : ℤ)) = x ^ n := by
    have h := zpow_mod_orderOf x n
    rwa [hord] at h
  rw [h1, hn]

private lemma a8jf_eq_one_of_mem_centralizer_of_center_eq_bot {G : Type*} [Group G]
    {X : Subgroup G} (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

theorem ggA8Nbr_spFrame
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J) (hInnL : GGInnerDiagOn Bs L)
    (ψ : StatedSp 3 (GaloisField 2 3) →* G) (hinj : Function.Injective ψ) (hrange : ψ.range = L)
    {e₀ : G} (he₀ : e₀ ∈ Bs ⊓ L) :
    ∃ (A₀ : StatedSp 3 (GaloisField 2 3)) (ζ : (GaloisField 2 3)ˣ) (hζ : ζ ^ 7 = 1),
      orderOf ζ = 7 ∧ (CoordSp.frameHom ψ A₀ hζ).range = Bs ⊓ L ∧
      (∀ b ∈ Bs, ∃ e ∈ Bs ⊓ L, ∃ k : ℕ, b = e * x ^ k) ∧
      (∃ β : Fin 3 → ZMod 7, CoordSp.SpAligned β ∧
        CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd β) = e₀) ∧
      ∃ ιB : Additive ↥Bs ≃+ (Fin 4 → ZMod 7),
        ιB (Additive.ofMul ⟨x, hcfg.tableB_facts.2.2.1⟩) = Pi.single 0 1 ∧
        (∀ t : Fin 3 → ZMod 7, ∃ hb : CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t) ∈ Bs,
          ιB (Additive.ofMul ⟨CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t), hb⟩) =
            (Fin.cons 0 t : Fin 4 → ZMod 7)) ∧
        ∀ (π : Equiv.Perm (Fin 3)) (η : Fin 3 → (ZMod 7)ˣ), (∀ i, η i ∈ CoordSp.signs 7) →
          ∃ φ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
            ιB (Additive.ofMul (φ b)) =
              (Fin.cons (ιB (Additive.ofMul b) 0)
                (fun i : Fin 3 => (η i : ZMod 7) * ιB (Additive.ofMul b) (π i).succ) :
                Fin 4 → ZMod 7) := by
  classical
  have hBs_ea : IsElemAbelian 7 Bs := hcfg.tableB_facts.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hBs_ge : 7 ^ 4 ≤ Nat.card Bs := hcfg.tableB_facts.2.2.2.2
  have hordx : orderOf x = 7 := hcfg.orderOf_x
  have hx7 : x ^ 7 = 1 := by rw [← hordx]; exact pow_orderOf_eq_one x
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hLx hy) x (by simp)).symm
  have hZSp : Subgroup.center (StatedSp 3 (GaloisField 2 3)) = ⊥ := by
    rw [Symplectic.center_eq 3 (GaloisField 2 3)]
    exact statedScalars_subgroupOf_statedSp_eq_bot_of_card (n := 3) (f := 3)
      (GaloisField.card 2 3 (by norm_num)) (by norm_num) (by norm_num)
  have hZL : Subgroup.center L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzL : (z : G) ∈ L := z.2
    have hzG : (z : G) ∈ ψ.range := by rw [hrange]; exact hzL
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hzG
    have haZ : a ∈ Subgroup.center (StatedSp 3 (GaloisField 2 3)) := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply hinj
      rw [map_mul, map_mul]
      have hcomm := Subgroup.mem_center_iff.mp hz
        (⟨ψ b, by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩ : L)
      have h2 : ψ b * (z : G) = (z : G) * ψ b := congrArg Subtype.val hcomm
      rw [← ha] at h2
      first | exact h2 | exact h2.symm
    rw [hZSp, Subgroup.mem_bot] at haZ
    apply Subtype.ext
    rw [← ha, haZ, map_one]
    rfl
  set E : Subgroup G := Bs ⊓ L with hE
  have hEab : IsElemAbelian 7 E := by
    rw [hE]; exact IsElemAbelian.mono hBs_ea inf_le_left
  have hnorm : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hInnL
  have hadm : StatedLieAdmissible .PSp 3 2 3 := by norm_num [StatedLieAdmissible]
  have hinner : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (m := 2) (f := 3) (by norm_num) hadm hInnL ψ hinj hrange
  have hsplit0 := ggBstar_split_of_inner hcfg.2.1 hZL hnorm hinner
  have hcard_split : Nat.card Bs =
      Nat.card E * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hE]; exact card_ggBstar_split hcfg.2.1 hZL hnorm hinner
  have hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 7 :=
    hcfg.card_bstar_inf_centralizer_L
  have hE_ge : 7 ^ 3 ≤ Nat.card E := by
    have h : 7 ^ 3 * 7 ≤ Nat.card E * 7 := by
      calc 7 ^ 3 * 7 = 7 ^ 4 := by norm_num
        _ ≤ Nat.card Bs := hBs_ge
        _ = Nat.card E * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hcard_split
        _ = Nat.card E * 7 := by rw [hcardC]
    exact Nat.le_of_mul_le_mul_right h (by norm_num)
  have hsplit : ∀ b ∈ Bs, ∃ e ∈ Bs ⊓ L, ∃ k : ℕ, b = e * x ^ k := by
    intro b hb
    obtain ⟨e, he, c, hc, hbc⟩ := hsplit0 b hb
    have hcz : c ∈ Subgroup.zpowers x := by
      rw [← hcfg.bstar_inf_centralizer_L]; exact hc
    obtain ⟨k, hk⟩ := a8jf_exists_nat_pow hordx hcz
    exact ⟨e, he, k, by rw [hbc, hk]⟩
  let E' : Subgroup (StatedSp 3 (GaloisField 2 3)) := E.comap ψ
  have hE'ab : IsElemAbelian 7 E' := IsElemAbelian.comap hEab hinj
  have hker_id :
      (MonoidHom.id (StatedSp 3 (GaloisField 2 3))).ker ≤
        Subgroup.center (StatedSp 3 (GaloisField 2 3)) := by
    rw [MonoidHom.ker_id]; exact bot_le
  have hC_id : Subgroup.centralizer
      (((MonoidHom.id (StatedSp 3 (GaloisField 2 3))).range : Set (StatedSp 3 (GaloisField 2 3)))) = ⊥ := by
    rw [show (MonoidHom.id (StatedSp 3 (GaloisField 2 3))).range = ⊤ from
        MonoidHom.range_eq_top.mpr (fun y => ⟨y, rfl⟩),
      Subgroup.coe_top, Subgroup.centralizer_univ]
    exact hZSp
  have hdiag' : ∀ a ∈ E',
      GGPsiInnerDiag (Symplectic.rootDatum 3 (GaloisField 2 3))
        (MonoidHom.id (StatedSp 3 (GaloisField 2 3))) a := by
    intro a _
    refine ⟨a⁻¹, ?_, ?_⟩
    · rw [MonoidHom.range_eq_top.mpr (fun y => ⟨y, rfl⟩)]
      exact Subgroup.mem_top a⁻¹
    · intro γ _
      exact ⟨1, (ggTorus (Symplectic.rootDatum 3 (GaloisField 2 3))).one_mem,
        fun z _ => by simp⟩
  obtain ⟨B₀, hB₀⟩ := spFrame_core (n := 3) (f := 3) (p := 7)
    (by norm_num) (by norm_num) (MonoidHom.id (StatedSp 3 (GaloisField 2 3))) hker_id hC_id
    (by norm_num) (by norm_num) hE'ab hdiag' (by norm_num)
  have hpF : 7 ∣ Nat.card (GaloisField 2 3) - 1 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 3) hpF
  have hζ : ζ ^ 7 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hFr_inj : Function.Injective (CoordSp.frameHom ψ B₀ hζ) :=
    CoordSp.frameHom_injective ψ B₀ hζ hinj hζo
  have hcard_range : Nat.card (CoordSp.frameHom ψ B₀ hζ).range = 7 ^ 3 := by
    have h := Subgroup.card_ker_mul_card_range (CoordSp.frameHom ψ B₀ hζ)
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hFr_inj, Subgroup.card_bot, one_mul] at h
    rw [h, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun]
    simp [ZMod.card]
  have hE_le_range : E ≤ (CoordSp.frameHom ψ B₀ hζ).range := by
    intro e he
    have he' : e ∈ Bs ⊓ L := hE ▸ he
    have heL : e ∈ L := (Subgroup.mem_inf.mp he').2
    rw [← hrange] at heL
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp heL
    have haE' : a ∈ E' := by
      rw [Subgroup.mem_comap, ha]; exact he
    obtain ⟨t, ht⟩ := hB₀ a haE'
    have ht' : a = RestSp.frameDiag B₀ t := by simpa using ht
    choose s hs using fun i => a8jf_exists_zeta_pow hζ hζo (t i)
    have hst : CoordSp.spDiag (F := GaloisField 2 3) (n := 3)
        (fun i => ζ ^ (s i).val) = CoordSp.spDiag t := by
      congr 1
      funext i
      exact hs i
    refine ⟨Multiplicative.ofAdd (fun i => s i), ?_⟩
    calc ψ (B₀ * CoordSp.spDiag (fun i => ζ ^ (s i).val) * B₀⁻¹)
        = ψ (B₀ * CoordSp.spDiag t * B₀⁻¹) := by rw [hst]
      _ = ψ (RestSp.frameDiag B₀ t) := by rw [CoordSp.frameDiag_eq]
      _ = ψ a := by rw [ht']
      _ = e := ha
  have hFr_B₀ : (CoordSp.frameHom ψ B₀ hζ).range = E :=
    (Subgroup.eq_of_le_of_card_ge hE_le_range (by rw [hcard_range]; exact hE_ge)).symm
  have he₀_range : e₀ ∈ (CoordSp.frameHom ψ B₀ hζ).range := by rw [hFr_B₀]; exact he₀
  obtain ⟨βu, hβu⟩ := he₀_range
  let β₀ : Fin 3 → ZMod 7 := Multiplicative.toAdd βu
  have hβ₀ : CoordSp.frameHom ψ B₀ hζ (Multiplicative.ofAdd β₀) = e₀ := by
    rw [show Multiplicative.ofAdd β₀ = βu from rfl]
    exact hβu
  let A₀ : StatedSp 3 (GaloisField 2 3) :=
    B₀ * (CoordSp.spPerm (CoordSp.alignFlip β₀) (Equiv.refl (Fin 3)))⁻¹
  let β : Fin 3 → ZMod 7 := fun i => (CoordSp.alignSign β₀ i : ZMod 7) * β₀ i
  have hal : CoordSp.SpAligned β := CoordSp.spAligned_align (by norm_num) β₀
  have hβe₀ : CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd β) = e₀ := by
    have hflip := CoordSp.frameHom_flip ψ B₀ hζ β₀ β₀
    change CoordSp.frameHom ψ
        (B₀ * (CoordSp.spPerm (CoordSp.alignFlip β₀) (Equiv.refl (Fin 3)))⁻¹) hζ
        (Multiplicative.ofAdd β) = e₀
    rw [hflip, hβ₀]
  have hηη : ∀ i, (CoordSp.alignSign β₀ i : ZMod 7) *
      (CoordSp.alignSign β₀ i : ZMod 7) = 1 := CoordSp.coe_alignSign_mul_self β₀
  have hι' : ∀ t : Fin 3 → ZMod 7,
      CoordSp.frameHom ψ A₀ hζ
          (Multiplicative.ofAdd fun i => (CoordSp.alignSign β₀ i : ZMod 7) * t i) =
        CoordSp.frameHom ψ B₀ hζ (Multiplicative.ofAdd t) := by
    intro t
    have hflip := CoordSp.frameHom_flip ψ B₀ hζ β₀ t
    change CoordSp.frameHom ψ
        (B₀ * (CoordSp.spPerm (CoordSp.alignFlip β₀) (Equiv.refl (Fin 3)))⁻¹) hζ
        (Multiplicative.ofAdd fun i => (CoordSp.alignSign β₀ i : ZMod 7) * t i) =
      CoordSp.frameHom ψ B₀ hζ (Multiplicative.ofAdd t)
    exact hflip
  have hrange_flip : (CoordSp.frameHom ψ A₀ hζ).range = (CoordSp.frameHom ψ B₀ hζ).range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Multiplicative.ofAdd fun i =>
        (CoordSp.alignSign β₀ i : ZMod 7) * Multiplicative.toAdd u i, ?_⟩
      rw [← hι' (fun i => (CoordSp.alignSign β₀ i : ZMod 7) * Multiplicative.toAdd u i)]
      congr 1
      apply Multiplicative.toAdd.injective
      funext i
      change (CoordSp.alignSign β₀ i : ZMod 7) *
        ((CoordSp.alignSign β₀ i : ZMod 7) * Multiplicative.toAdd u i) =
          Multiplicative.toAdd u i
      rw [← mul_assoc, hηη, one_mul]
    · rintro ⟨u, rfl⟩
      exact ⟨_, hι' (Multiplicative.toAdd u)⟩
  have hFr_A₀ : (CoordSp.frameHom ψ A₀ hζ).range = E := hrange_flip.trans hFr_B₀
  have hxnotL : x ∉ L := by
    intro hxL
    have h1 : x ∈ Subgroup.zpowers x ⊓ L := Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers x, hxL⟩
    have hbot : Subgroup.zpowers x ⊓ L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨hyx, hyL⟩ := Subgroup.mem_inf.mp hy
      exact a8jf_eq_one_of_mem_centralizer_of_center_eq_bot hZL hyL
        ((Subgroup.zpowers_le.mpr hxcent) hyx)
    rw [hbot, Subgroup.mem_bot] at h1
    have hx1 : x = 1 := h1
    have : orderOf x = 1 := by rw [hx1]; exact orderOf_one
    omega
  let ιT : (Fin 3 → ZMod 7) → G := fun t => CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t)
  have hιT_mem_L : ∀ t, ιT t ∈ L := fun t =>
    (Subgroup.mem_inf.mp (hFr_A₀ ▸ MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd t, rfl⟩)).2
  have hιT_mem : ∀ t, ιT t ∈ Bs := fun t =>
    (Subgroup.mem_inf.mp (hFr_A₀ ▸ MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd t, rfl⟩)).1
  have hιT_inj : Function.Injective ιT := by
    intro a b hab
    exact Multiplicative.ofAdd.injective
      ((CoordSp.frameHom_injective ψ A₀ hζ hinj hζo) hab)
  have hιT_zero : ιT 0 = 1 := by
    change CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd (0 : Fin 3 → ZMod 7)) = 1
    rw [show Multiplicative.ofAdd (0 : Fin 3 → ZMod 7) = 1 from rfl, map_one]
  have hιT_add : ∀ a b : Fin 3 → ZMod 7, ιT (a + b) = ιT a * ιT b := by
    intro a b
    change CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd (a + b)) =
      CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd a) *
        CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd b)
    rw [← map_mul]
    exact congrArg _ (show Multiplicative.ofAdd (a + b) =
      Multiplicative.ofAdd a * Multiplicative.ofAdd b from rfl)
  let ΦFun : (Fin 4 → ZMod 7) → ↥Bs := fun v =>
    ⟨x ^ (v 0).val * ιT (Fin.tail v),
      Bs.mul_mem (Bs.pow_mem hxBs _) (hιT_mem _)⟩
  have hΦFun_zero : ΦFun 0 = 1 := by
    apply Subtype.ext
    simp only [ΦFun, Pi.zero_apply, ZMod.val_zero, pow_zero, one_mul]
    have htail : Fin.tail (0 : Fin 4 → ZMod 7) = 0 := by funext i; rfl
    rw [htail, hιT_zero]
    rfl
  have hΦFun_add : ∀ v w : Fin 4 → ZMod 7, ΦFun (v + w) = ΦFun v * ΦFun w := by
    intro v w
    apply Subtype.ext
    simp only [ΦFun, Subgroup.coe_mul]
    have hpv : x ^ ((v + w) 0).val = x ^ (v 0).val * x ^ (w 0).val := by
      rw [show (v + w) 0 = v 0 + w 0 from rfl]
      exact a8jf_pow_val_add hx7 (v 0) (w 0)
    have htv : Fin.tail (v + w) = Fin.tail v + Fin.tail w := by funext i; rfl
    rw [hpv, htv, hιT_add]
    have hcomm : Commute (x ^ (w 0).val) (ιT (Fin.tail v)) :=
      (show Commute (ιT (Fin.tail v)) x from
        Subgroup.mem_centralizer_iff.mp hxcent (ιT (Fin.tail v)) (hιT_mem_L _)).symm.pow_left _
    calc x ^ (v 0).val * x ^ (w 0).val * (ιT (Fin.tail v) * ιT (Fin.tail w))
        = x ^ (v 0).val * (x ^ (w 0).val * ιT (Fin.tail v)) * ιT (Fin.tail w) := by group
      _ = x ^ (v 0).val * (ιT (Fin.tail v) * x ^ (w 0).val) * ιT (Fin.tail w) := by
            rw [hcomm.eq]
      _ = x ^ (v 0).val * ιT (Fin.tail v) * (x ^ (w 0).val * ιT (Fin.tail w)) := by group
  let Φ : (Fin 4 → ZMod 7) →+ Additive ↥Bs :=
    { toFun := fun v => Additive.ofMul (ΦFun v)
      map_zero' := by
        change Additive.ofMul (ΦFun 0) = (0 : Additive ↥Bs)
        rw [hΦFun_zero]; rfl
      map_add' := fun v w => by
        change Additive.ofMul (ΦFun (v + w)) =
          Additive.ofMul (ΦFun v) + Additive.ofMul (ΦFun w)
        rw [hΦFun_add]; rfl }
  have hsurjΦ : Function.Surjective Φ := by
    intro b
    let b' : ↥Bs := Additive.toMul b
    obtain ⟨e, he, c, hc, hbc⟩ := hsplit0 b' b'.2
    have he_range : e ∈ (CoordSp.frameHom ψ A₀ hζ).range := by rw [hFr_A₀]; exact he
    obtain ⟨u, hu⟩ := he_range
    have hc' : c ∈ Subgroup.zpowers x := by
      rw [← hcfg.bstar_inf_centralizer_L]; exact hc
    obtain ⟨k, hk⟩ := a8jf_exists_nat_pow hordx hc'
    refine ⟨Fin.cons (k : ZMod 7) (Multiplicative.toAdd u), ?_⟩
    change ΦFun (Fin.cons (k : ZMod 7) (Multiplicative.toAdd u)) = b'
    apply Subtype.ext
    simp only [ΦFun, Fin.cons_zero, Fin.tail_cons]
    have hku : ιT (Multiplicative.toAdd u) = e := by
      change CoordSp.frameHom ψ A₀ hζ (Multiplicative.toAdd u) = e
      exact hu
    have hkmod : x ^ (k % 7) = x ^ k := by
      conv_rhs => rw [← Nat.mod_add_div k 7]
      rw [pow_add, pow_mul, hx7, one_pow, mul_one]
    have hkval : x ^ ((k : ZMod 7)).val = c := by
      rw [ZMod.val_natCast, hkmod, hk]
    have heL : e ∈ L := (Subgroup.mem_inf.mp he).2
    calc x ^ ((k : ZMod 7)).val * ιT (Multiplicative.toAdd u)
        = c * e := by rw [hkval, hku]
      _ = e * c := (Subgroup.mem_centralizer_iff.mp hc.2 e heL).symm
      _ = b' := hbc.symm
  have hinjΦ : Function.Injective Φ := by
    intro v w hvw
    have hzero : Φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 : ΦFun (v - w) = 1 := by
      have h := congrArg Additive.toMul hzero
      simpa [Φ] using h
    have hcoe : x ^ ((v - w) 0).val * ιT (Fin.tail (v - w)) = 1 := by
      have h := congrArg (fun z : ↥Bs => (z : G)) h1
      simpa [ΦFun] using h
    have hxL : x ^ ((v - w) 0).val ∈ L := by
      have h1' : x ^ ((v - w) 0).val = (ιT (Fin.tail (v - w)))⁻¹ :=
        eq_inv_of_mul_eq_one_left hcoe
      rw [h1']
      exact L.inv_mem (hιT_mem_L _)
    have hxz : x ^ ((v - w) 0).val ∈ Subgroup.zpowers x :=
      Subgroup.mem_zpowers_iff.mpr
        ⟨(((v - w) 0).val : ℤ), by rw [zpow_natCast]⟩
    have hx1 : x ^ ((v - w) 0).val = 1 := by
      have hmem : x ^ ((v - w) 0).val ∈ Subgroup.zpowers x ⊓ L :=
        Subgroup.mem_inf.mpr ⟨hxz, hxL⟩
      have hbot : Subgroup.zpowers x ⊓ L = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        obtain ⟨hyx, hyL⟩ := Subgroup.mem_inf.mp hy
        exact a8jf_eq_one_of_mem_centralizer_of_center_eq_bot hZL hyL
          ((Subgroup.zpowers_le.mpr hxcent) hyx)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hval : ((v - w) 0).val = 0 := by
      have hdvd : 7 ∣ ((v - w) 0).val := by
        have := orderOf_dvd_of_pow_eq_one hx1
        rwa [hordx] at this
      have hlt := ZMod.val_lt ((v - w) 0)
      omega
    have h0 : (v - w) 0 = 0 := (ZMod.val_eq_zero _).mp hval
    have htail1 : ιT (Fin.tail (v - w)) = 1 := by
      rw [hx1, one_mul] at hcoe
      exact hcoe
    have htail0 : Fin.tail (v - w) = 0 :=
      hιT_inj (by rw [htail1, hιT_zero])
    have hsub0 : v - w = 0 := by
      have h := Fin.cons_self_tail (v - w)
      rw [h0, htail0] at h
      have h00 : (Fin.cons 0 0 : Fin 4 → ZMod 7) = 0 := by funext i; fin_cases i <;> rfl
      rw [h00] at h
      exact h.symm
    exact sub_eq_zero.mp hsub0
  let Φe : (Fin 4 → ZMod 7) ≃+ Additive ↥Bs :=
    AddEquiv.ofBijective Φ ⟨hinjΦ, hsurjΦ⟩
  let ιB : Additive ↥Bs ≃+ (Fin 4 → ZMod 7) := Φe.symm
  have hιB_PhiFun : ∀ v : Fin 4 → ZMod 7, ιB (Additive.ofMul (ΦFun v)) = v := by
    intro v
    change Φe.symm (Φ v) = v
    exact Φe.symm_apply_apply v
  have hιB_x : ιB (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 0 1 := by
    have hsingle : Φ (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) =
        Additive.ofMul ⟨x, hxBs⟩ := by
      change ΦFun (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) = ⟨x, hxBs⟩
      apply Subtype.ext
      have htail : Fin.tail (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) = 0 := by
        funext i
        rw [Fin.tail]
        exact Pi.single_eq_of_ne (by simp) 1
      haveI : Fact (1 < 7) := ⟨by norm_num⟩
      simp only [ΦFun, Pi.single_eq_same, htail, hιT_zero, ZMod.val_one]
      rw [pow_one, mul_one]
    exact (Φe.symm_apply_eq).mpr hsingle.symm
  have hιB_t : ∀ t : Fin 3 → ZMod 7,
      ∃ hb : CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t) ∈ Bs,
        ιB (Additive.ofMul ⟨CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t), hb⟩) =
          (Fin.cons 0 t : Fin 4 → ZMod 7) := by
    intro t
    refine ⟨hιT_mem t, ?_⟩
    have hsingle_t : Φ (Fin.cons 0 t) = Additive.ofMul ⟨ιT t, hιT_mem t⟩ := by
      change ΦFun (Fin.cons 0 t) = ⟨ιT t, hιT_mem t⟩
      apply Subtype.ext
      simp only [ΦFun, Fin.cons_zero, Fin.tail_cons, ZMod.val_zero, pow_zero, one_mul]
    change ιB (Additive.ofMul ⟨ιT t, hιT_mem t⟩) = Fin.cons 0 t
    exact (Φe.symm_apply_eq).mpr hsingle_t.symm
  have hmoves : ∀ (π : Equiv.Perm (Fin 3)) (η : Fin 3 → (ZMod 7)ˣ),
      (∀ i, η i ∈ CoordSp.signs 7) →
      ∃ φ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
        ιB (Additive.ofMul (φ b)) =
          (Fin.cons (ιB (Additive.ofMul b) 0)
            (fun i : Fin 3 => (η i : ZMod 7) * ιB (Additive.ofMul b) (π i).succ) :
            Fin 4 → ZMod 7) := by
    intro π η hη
    obtain ⟨w, hw, hws⟩ := CoordSp.exists_move_mem ψ A₀ hζ hFr_A₀ π η hη
    have hwL : w ∈ L := by rw [← hrange]; exact (Subgroup.mem_inf.mp hw).1
    have hwE : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.mp hw).2
    have hcomm_xw : w * x = x * w := Subgroup.mem_centralizer_iff.mp hxcent w hwL
    have hwx : w * x * w⁻¹ = x := by rw [hcomm_xw]; group
    have hwix : w⁻¹ * x * w = x := by
      calc w⁻¹ * x * w = w⁻¹ * (x * w) := by group
        _ = w⁻¹ * (w * x) := by rw [hcomm_xw.symm]
        _ = x := by group
    have hwNx : w ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      congr 1
    have hBs_eq : Bs = E ⊔ Subgroup.zpowers x := by
      apply le_antisymm
      · intro b hb
        obtain ⟨e, he, c, hc, hbc⟩ := hsplit0 b hb
        have hc' : c ∈ Subgroup.zpowers x := by
          rw [← hcfg.bstar_inf_centralizer_L]; exact hc
        rw [hbc]
        exact (E ⊔ Subgroup.zpowers x).mul_mem (Subgroup.mem_sup_left he)
          (Subgroup.mem_sup_right hc')
      · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxBs)
    have hwN : w ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [hBs_eq]
      exact Subgroup.inf_normalizer_le_normalizer_sup E (Subgroup.zpowers x) ⟨hwE, hwNx⟩
    have hwN' : w⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hwN
    refine ⟨ggConjAut Bs hwN', ggConjAut_mem_ggAutomizer (H := L) (L.inv_mem hwL) hwN', fun b => ?_⟩
    set v : Fin 4 → ZMod 7 := ιB (Additive.ofMul b) with hv
    have hvPhi : Φ (ιB (Additive.ofMul b)) = Additive.ofMul b :=
      Φe.apply_symm_apply (Additive.ofMul b)
    have hb_eq : ΦFun v = b := hvPhi
    have hact : ggConjAut Bs hwN' (ΦFun v) =
        ΦFun (Fin.cons (v 0)
          (fun i : Fin 3 => (η i : ZMod 7) * (Fin.tail v) (π i))) := by
      apply Subtype.ext
      have hws_v := hws (Fin.tail v)
      rw [ggConjAut_apply]
      simp only [ΦFun, Subgroup.coe_mk, inv_inv]
      rw [Fin.cons_zero, Fin.tail_cons]
      have hwxpow : w⁻¹ * x ^ (v 0).val * w = x ^ (v 0).val := by
        have hc : Commute (x ^ (v 0).val) w :=
          (show Commute x w from hcomm_xw.symm).pow_left (v 0).val
        calc w⁻¹ * x ^ (v 0).val * w = w⁻¹ * (x ^ (v 0).val * w) := by group
          _ = w⁻¹ * (w * x ^ (v 0).val) := by rw [hc.eq]
          _ = x ^ (v 0).val := by group
      calc w⁻¹ * (x ^ (v 0).val * ιT (Fin.tail v)) * w
          = (w⁻¹ * x ^ (v 0).val * w) * (w⁻¹ * ιT (Fin.tail v) * w) := by group
        _ = x ^ (v 0).val * ιT (fun i : Fin 3 => (η i : ZMod 7) * (Fin.tail v) (π i)) := by
              rw [hwxpow, hws_v]
    have hφb : ggConjAut Bs hwN' b =
        ΦFun (Fin.cons (v 0)
          (fun i : Fin 3 => (η i : ZMod 7) * (Fin.tail v) (π i))) := by
      rw [← hb_eq]
      exact hact
    calc ιB (Additive.ofMul (ggConjAut Bs hwN' b))
        = ιB (Additive.ofMul (ΦFun (Fin.cons (v 0)
            (fun i : Fin 3 => (η i : ZMod 7) * (Fin.tail v) (π i))))) := by rw [hφb]
      _ = Fin.cons (v 0) (fun i : Fin 3 => (η i : ZMod 7) * (Fin.tail v) (π i)) :=
            hιB_PhiFun _
      _ = Fin.cons (ιB (Additive.ofMul b) 0)
            (fun i : Fin 3 => (η i : ZMod 7) * ιB (Additive.ofMul b) (π i).succ) := by
            rw [hv]
            funext j
            fin_cases j <;> simp [Fin.tail]
  refine ⟨A₀, ζ, hζ, hζo, hFr_A₀, hsplit, ⟨β, hal, hβe₀⟩, ιB, ?_, ?_, ?_⟩
  · exact hιB_x
  · exact hιB_t
  · exact hmoves

end CFSG.StandardType.A8Coord

end
