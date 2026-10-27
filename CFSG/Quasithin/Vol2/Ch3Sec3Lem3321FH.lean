module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FG
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321E
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FB

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.ChiefCount
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.Lift
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftPre_le)
open CFSG.Quasithin.H13.Gen3324 (pre₀ mem_pre₀)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem relIndex_le_three [Finite G] {K : Subgroup G} (ρ : ↥K →* SL2F2) :
    (oTwoUpper K ⊓ pre₀ ρ ⊥).relIndex (oTwoUpper K) ≤ 3 := by
  set X := oTwoUpper K with hX
  have hXK : X ≤ K := oTwoUpper_le K
  set f : ↥X →* SL2F2 := ρ.comp (Subgroup.inclusion hXK) with hf
  have hXA : X ≤ pre₀ ρ A3 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxK, hodd⟩
    refine (mem_pre₀ ρ).2 ⟨hxK, mem_A3_of_odd hodd ?_⟩
    rw [← map_pow]
    have : (⟨x, hxK⟩ : ↥K) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hrange : f.range ≤ A3 := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨hyK, hyA⟩ := (mem_pre₀ ρ).1 (hXA y.2)
    exact hyA
  have hker : f.ker = (pre₀ ρ ⊥).subgroupOf X := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_pre₀]
    exact ⟨fun h1 => ⟨hXK y.2, Subgroup.mem_bot.2 h1⟩,
      fun ⟨_, h1⟩ => Subgroup.mem_bot.1 h1⟩
  have hcard_ker : Nat.card ↥f.ker = Nat.card ↥(X ⊓ pre₀ ρ ⊥) := by
    rw [hker, ← Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hcard_ker] at h1
  have h2 := Subgroup.relIndex_mul_card (X ⊓ pre₀ ρ ⊥) X
  rw [inf_eq_left.2 (inf_le_left : X ⊓ pre₀ ρ ⊥ ≤ X)] at h2
  have hpos : 0 < Nat.card ↥(X ⊓ pre₀ ρ ⊥) := Nat.card_pos
  have h3 : (X ⊓ pre₀ ρ ⊥).relIndex X = Nat.card ↥f.range :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1)
  rw [h3]
  calc Nat.card ↥f.range ≤ Nat.card ↥A3 := Subgroup.card_le_of_le hrange
    _ = 3 := card_A3

variable [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem relIndex_le_32 (hD : FData G T M L D α) {P : Subgroup SL4} (hP : P ≤ P2)
    (blk : ↥P2 →* SL2F2) {X : Subgroup G} (hXK : X ≤ liftPre α P)
    (hVO : pCoreOf 2 L = vPlus L T) (hRT : pre₀ (blk.comp (toP2 α hP)) ⊥ ≤ T)
    (hVR : vPlus L T ≤ pre₀ (blk.comp (toP2 α hP)) ⊥) {t : SL4} (htU : t ∈ FLc.Ut 4)
    (htP : t ∈ P2) (htb : blk ⟨t, htP⟩ ≠ 1) :
    (X ⊓ vPlus L T).relIndex (X ⊓ pre₀ (blk.comp (toP2 α hP)) ⊥) ≤ 32 := by
  set R := pre₀ (blk.comp (toP2 α hP)) ⊥ with hR
  have hQL : X ⊓ R ≤ L := inf_le_left.trans (hXK.trans (liftPre_le α P))
  have h1 := card_eq_mul hD.ker hQL
  have hinf : X ⊓ R ⊓ pCoreOf 2 L = X ⊓ vPlus L T := by
    rw [hVO]
    exact le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx => ⟨⟨hx.1, hVR hx.2⟩, hx.2⟩
  rw [hinf] at h1
  have h2 := Subgroup.relIndex_mul_card (X ⊓ vPlus L T) (X ⊓ R)
  have hle : X ⊓ vPlus L T ≤ X ⊓ R := fun x hx => ⟨hx.1, hVR hx.2⟩
  rw [inf_eq_left.2 hle] at h2
  have hpos : 0 < Nat.card ↥(X ⊓ vPlus L T) := Nat.card_pos
  have h3 : (X ⊓ vPlus L T).relIndex (X ⊓ R) =
      Nat.card ↥(α.comp (Subgroup.inclusion hQL)).range :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans (h1.trans (mul_comm _ _)))
  rw [h3]
  refine card_le_32 ?_ htU ?_
  · rintro _ ⟨x, rfl⟩
    exact hD.mem_Ut _ (hRT x.2.2)
  · rintro ⟨x, hx⟩
    obtain ⟨hxK, hx1⟩ := (mem_pre₀ _).1 x.2.2
    apply htb
    have e : (⟨t, htP⟩ : ↥P2) = toP2 α hP ⟨x, hxK⟩ := Subtype.ext hx.symm
    rw [e]
    exact Subgroup.mem_bot.1 hx1

theorem center_ne_bot (h : Hyp331 G T M L D) {X : Subgroup G}
    (hXZ : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Subgroup.center ↥(conjClosure X D ⊔ T) ≠ ⊥ := by
  set Z := quasithinOmegaOneCenter T with hZ
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot h.sylow.1 h.toSetup331.T_ne_bot
  have hDZ : D ≤ Subgroup.normalizer (Z : Set G) :=
    h.DN.trans (Hyp331.normalizer_le_normalizer_of_characteristic hZT
      (CFSG.QuasithinUnique.L246C127.characteristic_omegaOneCenter T))
  have hcent : conjClosure X D ⊔ T ≤ Subgroup.centralizer (Z : Set G) := by
    refine sup_le (conjClosure_le fun d hd x hx => ?_)
      (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : d⁻¹ * w * d ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (hDZ (D.inv_mem hd)) w).mp hw
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 (hXZ hx) _ hw'
    calc w * (d * x * d⁻¹) = d * ((d⁻¹ * w * d) * x) * d⁻¹ := by group
      _ = d * (x * (d⁻¹ * w * d)) * d⁻¹ := by rw [h1]
      _ = d * x * d⁻¹ * w := by group
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ1
  have hzmem : z ∈ conjClosure X D ⊔ T := Subgroup.mem_sup_right (hZT hzZ)
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨z, hzmem⟩, Subgroup.mem_center_iff.2 fun g => ?_⟩,
    fun h1 => ?_⟩
  · apply Subtype.ext
    show (g : G) * z = z * g
    exact (Subgroup.mem_centralizer_iff.1 (hcent g.2) z hzZ).symm
  · have h2 : z = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center ↥(conjClosure X D ⊔ T)) =>
        ((w : ↥(conjClosure X D ⊔ T)) : G)) h1
      simpa using this
    exact hz1 (Subtype.ext h2)

omit [Finite G] in
theorem two_pow_of_leviA (hker : α.ker = CFSG.pCore 2 ↥L)
    (g : ↥(liftPre α (FLc.QI 4 {2, 3}))) (hg : leviA α g = 1) :
    ∃ n : ℕ, (g : G) ^ 2 ^ n = 1 := by
  set p := toP2 α QI23_le_P2 g with hp
  have hA : blkA p = 1 := hg
  have hC : blkC p * blkC p = 1 := blkC_sq_of_QI23 (mem_of_mem_liftPre g.2)
  have hU : ((p * p : ↥P2) : SL4) ∈ FLc.Ut 4 :=
    mem_Ut_of_blk (by rw [map_mul, hA, mul_one]) (by rw [map_mul, hC])
  have hgL : (g : G) * g ∈ L := L.mul_mem (liftPre_le α _ g.2) (liftPre_le α _ g.2)
  have e : α ⟨(g : G) * g, hgL⟩ = ((p * p : ↥P2) : SL4) := by
    rw [Subgroup.coe_mul, hp, coe_toP2, ← map_mul]
    rfl
  obtain ⟨n, hn⟩ := exists_pow_of_mem_Ut hker (x := ⟨(g : G) * g, hgL⟩) (by rw [e]; exact hU)
  refine ⟨n + 1, ?_⟩
  rw [pow_succ', pow_mul, pow_two]
  exact hn

omit [Finite G] in
theorem two_pow_of_leviC (hker : α.ker = CFSG.pCore 2 ↥L)
    (g : ↥(liftPre α (FLc.QI 4 {1, 2}))) (hg : leviC α g = 1) :
    ∃ n : ℕ, (g : G) ^ 2 ^ n = 1 := by
  set p := toP2 α QI12_le_P2 g with hp
  have hC : blkC p = 1 := hg
  have hA : blkA p * blkA p = 1 := blkA_sq_of_QI12 (mem_of_mem_liftPre g.2)
  have hU : ((p * p : ↥P2) : SL4) ∈ FLc.Ut 4 :=
    mem_Ut_of_blk (by rw [map_mul, hA]) (by rw [map_mul, hC, mul_one])
  have hgL : (g : G) * g ∈ L := L.mul_mem (liftPre_le α _ g.2) (liftPre_le α _ g.2)
  have e : α ⟨(g : G) * g, hgL⟩ = ((p * p : ↥P2) : SL4) := by
    rw [Subgroup.coe_mul, hp, coe_toP2, ← map_mul]
    rfl
  obtain ⟨n, hn⟩ := exists_pow_of_mem_Ut hker (x := ⟨(g : G) * g, hgL⟩) (by rw [e]; exact hU)
  refine ⟨n + 1, ?_⟩
  rw [pow_succ', pow_mul, pow_two]
  exact hn

theorem blkA_elU3_ne : blkA ⟨elU3 0, Ut_le_P2 (elU3_mem 0)⟩ ≠ 1 := by
  intro h1
  have h2 := congrArg (fun A : SL2F2 => (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1) h1
  simp only [coe_blkA, blkAM_apply] at h2
  revert h2
  decide

theorem blkC_elU3_ne : blkC ⟨elU3 2, Ut_le_P2 (elU3_mem 2)⟩ ≠ 1 := by
  intro h1
  have h2 := congrArg (fun A : SL2F2 => (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1) h1
  simp only [coe_blkC, blkCM_apply] at h2
  revert h2
  decide

end CFSG.Quasithin.H13.L3321
