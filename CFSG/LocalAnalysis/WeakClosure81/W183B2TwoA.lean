module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
import CFSG.LocalAnalysis.WeakClosure81.W183Abs1
import CFSG.LocalAnalysis.WeakClosure81.W183B2CoreKAux
import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183b2_exists_mul_of_mem_sup {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, a * b = x)
    (fun y hy => ?_) ?_ (fun y z _ _ ihy ihz => ?_) (fun y _ ihy => ?_) hx
  · rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := ihy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
      _ = (a * b)⁻¹ := by rw [hcomm a ha b hb]

private theorem w183b2_fixSub_sup (A B : Subgroup (LGL 2 V)) :
    fixSub (A ⊔ B) = fixSub A ⊓ fixSub B := by
  refine le_antisymm ?_ ?_
  · intro v hv
    exact ⟨fun a ha => hv a (Subgroup.mem_sup_left ha),
      fun b hb => hv b (Subgroup.mem_sup_right hb)⟩
  · intro v hv
    let S : Subgroup (LGL 2 V) :=
      { carrier := {g | g v = v}
        one_mem' := rfl
        mul_mem' := by
          intro a b ha hb
          show a (b v) = v
          rw [hb, ha]
        inv_mem' := by
          intro a ha
          show a⁻¹ v = v
          calc a⁻¹ v = a⁻¹ (a v) := by rw [ha]
            _ = v := LinearEquiv.symm_apply_apply a v }
    have hle : A ⊔ B ≤ S :=
      sup_le (fun a ha => hv.1 a ha) (fun b hb => hv.2 b hb)
    exact fun g hg => hle hg

theorem w183b2_VA_inf_fixSub_of_quasi {i : ℕ} (h131 : Assumption131 Y Γ VA i)
    {D L : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (hLY : L ≤ Y)
    (hDnorm : D ≤ Subgroup.normalizer (L : Set (LGL 2 V)))
    (hDcent : ¬ D ≤ Subgroup.centralizer (L : Set (LGL 2 V))) :
    VA D ⊓ fixSub L = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  have hLnorm : L ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := fun l hl =>
    h131.stabilizer_le_normalizer hD hv.1 hv0 (hLY hl) (hv.2 l hl)
  have hKnorm : ((D ⊓ L).subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hLnorm g.2) (n : LGL 2 V)).mp hn.1
    · exact L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
  haveI := hKnorm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hLq
    ((D ⊓ L).subgroupOf L) with hbot | htop
  · have hKbot : D ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hxc : (⟨x, hx.2⟩ : ↥L) ∈ Subgroup.center ↥L :=
        hbot (by rw [Subgroup.mem_subgroupOf]; exact hx)
      have hx2 : x ^ 2 = 1 := (h131.isElemAb D hD).2 x hx.1
      let z : ↥(Subgroup.center ↥L) := ⟨⟨x, hx.2⟩, hxc⟩
      have hz2 : z ^ 2 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [z] using hx2
      have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have hdvd' : orderOf z ∣ Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard _
      have h1 : orderOf z = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact h
        · exfalso
          rw [h] at hdvd'
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd')
      have h2 : z = 1 := orderOf_eq_one_iff.mp h1
      exact congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : LGL 2 V)) h2
    exact hDcent (fun d hd => by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcomm : d * l * d⁻¹ * l⁻¹ = 1 := by
        have h1 : d * l * d⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hDnorm hd) l).mp hl
        have h2 : l * d⁻¹ * l⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp (hLnorm hl) d⁻¹).mp (D.inv_mem hd)
        have hmem : d * l * d⁻¹ * l⁻¹ ∈ D ⊓ L := by
          refine ⟨?_, ?_⟩
          · rw [show d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) by group]
            exact D.mul_mem hd h2
          · exact L.mul_mem h1 (L.inv_mem hl)
        rw [hKbot, Subgroup.mem_bot] at hmem
        exact hmem
      have hdl : d * l = l * d := by
        refine mul_inv_eq_one.mp ?_
        rw [mul_inv_rev, ← mul_assoc]
        exact hcomm
      exact hdl.symm)
  · have hLD : L ≤ D := by
      intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (D ⊓ L).subgroupOf L := by rw [htop]; trivial
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem.1
    obtain ⟨a, ha, b, hb, hab⟩ := W183K3.quasi_exists_noncomm hLq
    exact hab (IsElemAbelian.comm (h131.isElemAb D hD) (hLD ha) (hLD hb))

private theorem w183b2_odd_card_center_of_simple {L : Subgroup (LGL 2 V)} (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
  haveI : IsSimpleGroup ↥L := hs
  have hc : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      have hz : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := by rw [h]; trivial
      exact hab (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b, hb⟩).symm)
  rw [hc]
  simp

private theorem w183b2_VA_inf_fixSub_of_simple {i : ℕ} (h131 : Assumption131 Y Γ VA i)
    {D L : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hLsimple : IsSimpleGroup ↥L) (hLnonab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (hLY : L ≤ Y)
    (hDnorm : D ≤ Subgroup.normalizer (L : Set (LGL 2 V)))
    (hDcent : ¬ D ≤ Subgroup.centralizer (L : Set (LGL 2 V))) :
    VA D ⊓ fixSub L = ⊥ :=
  w183b2_VA_inf_fixSub_of_quasi h131 hD (w183b2_quasi_of_simple_nonab hLsimple hLnonab)
    (w183b2_odd_card_center_of_simple hLsimple hLnonab) hLY hDnorm hDcent

theorem Br2TwoComp.mem_normalizer_iff (h : Br2TwoComp Y T L₁ L₂) {y : LGL 2 V} (hy : y ∈ Y) :
    y ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ↔
      y ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  constructor
  · intro hy1
    have h1 : cj y L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy1
    rcases h.perm y hy with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    · exact absurd (h1.symm.trans h2) h.ne
  · intro hy2
    have h2 : cj y L₂ = L₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy2
    rcases h.perm y hy with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
    · exact absurd (h2.symm.trans h1) (Ne.symm h.ne)

theorem w183b2_two_fixSub_eq_bot (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂) : fixSub (L₁ ⊔ L₂) = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ t ∈ T, ∀ w ∈ fixSub (L₁ ⊔ L₂), t w ∈ fixSub (L₁ ⊔ L₂) := by
    intro t ht w hw l hl
    have htY : t ∈ Y := hc.sylow.le ht
    have hcj : cj t (L₁ ⊔ L₂) = L₁ ⊔ L₂ := by
      rcases hL.perm t htY with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [show cj t (L₁ ⊔ L₂) = cj t L₁ ⊔ cj t L₂ from
          Subgroup.map_sup L₁ L₂ (MulAut.conj t).toMonoidHom, h1, h2]
      · rw [show cj t (L₁ ⊔ L₂) = cj t L₁ ⊔ cj t L₂ from
          Subgroup.map_sup L₁ L₂ (MulAut.conj t).toMonoidHom, h1, h2, sup_comm]
    have hmem : t⁻¹ * l * t ∈ L₁ ⊔ L₂ := by
      have hmem' : l ∈ cj t (L₁ ⊔ L₂) := by rw [hcj]; exact hl
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hmem'
      have : a = t⁻¹ * l * t := by
        rw [← hae]
        change a = t⁻¹ * MulAut.conj t a * t
        rw [MulAut.conj_apply]
        group
      rwa [← this]
    calc l (t w) = (l * t) w := (LinearEquiv.mul_apply l t w).symm
      _ = (t * (t⁻¹ * l * t)) w := by congr 1; group
      _ = t ((t⁻¹ * l * t) w) := LinearEquiv.mul_apply t (t⁻¹ * l * t) w
      _ = t w := by rw [hw _ hmem]
  obtain ⟨w, hwW, hw0, hwT⟩ :=
    exists_fixed_of_isPGroup (p := 2) hc.sylow.isPGroup hne hinv
  have hwZs : w ∈ Zs := by rw [hc.zs_eq]; exact hwT
  obtain ⟨y, hyY, hyw⟩ := hc.zs_nofix w hwZs hw0
  obtain ⟨l, hl, t, ht, rfl⟩ := hL.gen y hyY
  have htw : t w = w := hwT t ht
  have hlw : l w = w := hwW l hl
  exact hyw (by rw [LinearEquiv.mul_apply, htw, hlw])

theorem w183b2_two_top_eq (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2TwoComp Y T L₁ L₂) :
    Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ = ⊤ := by
  refine le_antisymm le_top ?_
  have hle : (⨆ y ∈ Y, conjSub y Zs) ≤ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
    refine iSup₂_le fun y hy => ?_
    change Zs.map (y : V →ₗ[ZMod 2] V) ≤ _
    rw [Submodule.map_le_iff_le_comap]
    intro z hz
    obtain ⟨l, hl, t, ht, rfl⟩ := hL.gen y hy
    rw [Submodule.mem_comap]
    simp only [LinearEquiv.coe_toLinearMap]
    have htz : t z = z := by
      have hzT : z ∈ fixSub T := by rw [← hc.zs_eq]; exact hz
      exact hzT t ht
    rw [LinearEquiv.mul_apply, htz]
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := w183b2_exists_mul_of_mem_sup hL.comm hl
    rw [LinearEquiv.mul_apply]
    have h1 : l₁ (l₂ z) - l₂ z ∈ commSpace L₁ ⊤ :=
      sub_mem_commSpace (K := L₁) (U := ⊤) hl₁ trivial
    have h2 : l₂ z - z ∈ commSpace L₂ ⊤ :=
      sub_mem_commSpace (K := L₂) (U := ⊤) hl₂ trivial
    have hsum : l₁ (l₂ z) - z = (l₁ (l₂ z) - l₂ z) + (l₂ z - z) := by abel
    have hzU : z ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ :=
      Submodule.mem_sup_left (Submodule.mem_sup_left hz)
    have hmem : l₁ (l₂ z) - z ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
      rw [hsum]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_sup_right h1)) (Submodule.mem_sup_right h2)
    have hfin : l₁ (l₂ z) ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
      have h := Submodule.add_mem _ hzU hmem
      rwa [show z + (l₁ (l₂ z) - z) = l₁ (l₂ z) by abel] at h
    exact hfin
  rwa [hc.zs_gen] at hle

theorem w183b2_two_VA_inf_fixSub (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hmem : D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hD₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hD₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V))) :
    VA D ⊓ fixSub L₂ = ⊥ ∧ VA D ⊓ fixSub L₁ = ⊥ := by
  have hDY : D ≤ Y := hc.h131.le_G D hD
  refine ⟨?_, ?_⟩
  · exact w183b2_VA_inf_fixSub_of_simple hc.h131 hD hL.simple₂ hL.nonab₂ hL.le₂
      (fun d hd => (Br2TwoComp.mem_normalizer_iff hL (hDY hd)).mp (hmem hd)) hD₁
  · exact w183b2_VA_inf_fixSub_of_simple hc.h131 hD hL.simple₁ hL.nonab₁ hL.le₁ hmem hD₂

theorem w183b2_finrank_comm_le {D B : Subgroup (LGL 2 V)} (hDe : IsElemAbelian 2 D)
    (hDq : commSpace D (commSub D) = ⊥) (hBD : B ≤ D) {e : V} (he : e ∈ fixSub B) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w : V | ∃ d ∈ D, w = d e - e}) ≤
      mOf D B := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htriv : ∀ d ∈ D, ∀ u ∈ commSub D, d u = u := commSpace_eq_bot_iff.mp hDq
  let φ : ↥D →* Multiplicative V :=
    { toFun := fun d => Multiplicative.ofAdd ((d : LGL 2 V) e - e)
      map_one' := by simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        show (((a * b : ↥D) : LGL 2 V) e - e) =
          ((a : LGL 2 V) e - e) + ((b : LGL 2 V) e - e)
        have hb : (b : LGL 2 V) e - e ∈ commSub D := sub_mem_commSub (A := D) b.2 e
        have hfix : (a : LGL 2 V) ((b : LGL 2 V) e - e) = (b : LGL 2 V) e - e :=
          htriv a a.2 _ hb
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
        have haux : (a : LGL 2 V) ((b : LGL 2 V) e) =
            (a : LGL 2 V) ((b : LGL 2 V) e - e) + (a : LGL 2 V) e := by
          conv_lhs => rw [← sub_add_cancel ((b : LGL 2 V) e) e]
          rw [map_add]
        rw [haux, hfix]
        abel }
  let A : AddSubgroup V := Subgroup.toAddSubgroup' φ.range
  have hmemA : ∀ a : V, a ∈ A ↔ ∃ d ∈ D, a = d e - e := by
    intro a
    rw [Subgroup.mem_toAddSubgroup', MonoidHom.mem_range]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, d.2, (Multiplicative.ofAdd.injective hd).symm⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hT : Submodule.span (ZMod 2) {w : V | ∃ d ∈ D, w = d e - e} =
      AddSubgroup.toZModSubmodule 2 A := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro w hw
      change w ∈ A
      exact (hmemA w).mpr hw
    · intro w hw
      change w ∈ A at hw
      exact Submodule.subset_span ((hmemA w).mp hw)
  have hker : B.subgroupOf D ≤ φ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd ((b : LGL 2 V) e - e) = 1
    have hbe : (b : LGL 2 V) e - e = 0 := by
      rw [sub_eq_zero]
      rw [Subgroup.mem_subgroupOf] at hb
      exact he (b : LGL 2 V) hb
    rw [hbe]
    rfl
  have hindex : φ.ker.index ≤ (B.subgroupOf D).index := Subgroup.index_antitone hker
  have hcard : Nat.card (AddSubgroup.toZModSubmodule 2 A) = Nat.card φ.range :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.ofAdd (x : V), by
          rw [MonoidHom.mem_range]
          obtain ⟨d, hd, hxd⟩ := (hmemA (x : V)).mp x.2
          exact ⟨⟨d, hd⟩, by rw [hxd]; rfl⟩⟩
        invFun := fun y => ⟨Multiplicative.toAdd (y : Multiplicative V), by
          obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp y.2
          exact (hmemA (Multiplicative.toAdd (y : Multiplicative V))).mpr
            ⟨d, d.2, by rw [← hd]; rfl⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w : V | ∃ d ∈ D, w = d e - e})
      = Nat.log 2 (Nat.card (Submodule.span (ZMod 2) {w : V | ∃ d ∈ D, w = d e - e})) := by
        rw [card_eq_pow_finrank, Nat.log_pow (by norm_num : 1 < 2)]
    _ = Nat.log 2 (Nat.card (AddSubgroup.toZModSubmodule 2 A)) := by rw [hT]
    _ = Nat.log 2 (Nat.card φ.range) := by rw [hcard]
    _ = Nat.log 2 (φ.ker.index) := by rw [← Subgroup.index_ker]
    _ ≤ Nat.log 2 ((B.subgroupOf D).index) := Nat.log_mono_right hindex
    _ = mOf D B := rfl

theorem w183b2_two_false_of_mod (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂)
    (hmem : ∀ D ∈ Γ, D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hDT : D ≤ T)
    (hD₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hD₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hmod : commSpace L₂ (commSpace L₁ ⊤) = ⊥ ∧ commSpace L₁ (commSpace L₂ ⊤) = ⊥) : False := by
  have hDe : IsElemAbelian 2 D := hc.h131.isElemAb D hD
  have hDq : commSpace D (commSub D) = ⊥ := hc.h131.quadratic D hD
  obtain ⟨B, hBD, hno, hne⟩ := hc.noOffender D hD
  have hle : fixSub D ≤ fixSub B := fun v hv b hb => hv b (hBD hb)
  have hlt : (fixSub D : Set V) ⊂ (fixSub B : Set V) := by
    rw [Set.ssubset_def]
    exact ⟨hle, fun hB => hne (le_antisymm hle hB)⟩
  obtain ⟨e₀, he₀B, he₀D⟩ := Set.exists_of_ssubset hlt
  have he₀U : e₀ ∈ Zs ⊔ commSpace L₁ ⊤ ⊔ commSpace L₂ ⊤ := by
    rw [w183b2_two_top_eq hc.toBr1Base hL]; trivial
  obtain ⟨y, hy, e₂, he₂, hye₂⟩ := Submodule.mem_sup.mp he₀U
  obtain ⟨z, hz, e₁, he₁, hze₁⟩ := Submodule.mem_sup.mp hy
  have he₀ : e₀ = z + e₁ + e₂ := by rw [← hye₂, ← hze₁]
  have hzT : z ∈ fixSub T := by rw [← hc.zs_eq]; exact hz
  have hzD : z ∈ fixSub D := fun d hd => hzT d (hDT hd)
  have hzB : z ∈ fixSub B := fun b hb => hzD b (hBD hb)
  have heB : e₁ + e₂ ∈ fixSub B := by
    have h : e₀ - z ∈ fixSub B := Submodule.sub_mem _ he₀B hzB
    rwa [show e₀ - z = e₁ + e₂ by rw [he₀]; abel] at h
  have heD : e₁ + e₂ ∉ fixSub D := by
    intro h
    apply he₀D
    rw [he₀, add_assoc]
    exact Submodule.add_mem _ hzD h
  have hDnorm₁ : D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) := hmem D hD
  have hDnorm₂ : D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := fun d hd =>
    (Br2TwoComp.mem_normalizer_iff hL (hc.h131.le_G D hD hd)).mp (hmem D hD hd)
  have hinv₁ : Invariant D (commSpace L₁ ⊤) :=
    invariant_commSpace (fun d hd l hl => (Subgroup.mem_normalizer_iff.mp (hDnorm₁ hd) l).mp hl)
      (fun _ _ _ _ => trivial)
  have hinv₂ : Invariant D (commSpace L₂ ⊤) :=
    invariant_commSpace (fun d hd l hl => (Subgroup.mem_normalizer_iff.mp (hDnorm₂ hd) l).mp hl)
      (fun _ _ _ _ => trivial)
  have hE₁fix : commSpace L₁ ⊤ ≤ fixSub L₂ :=
    fun u hu => fun l hl => (commSpace_eq_bot_iff.mp hmod.1) l hl u hu
  have hE₂fix : commSpace L₂ ⊤ ≤ fixSub L₁ :=
    fun u hu => fun l hl => (commSpace_eq_bot_iff.mp hmod.2) l hl u hu
  have hEinf : commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤
        ≤ fixSub L₂ ⊓ fixSub L₁ := inf_le_inf hE₁fix hE₂fix
      _ = fixSub L₁ ⊓ fixSub L₂ := inf_comm _ _
      _ = fixSub (L₁ ⊔ L₂) := (w183b2_fixSub_sup L₁ L₂).symm
      _ = ⊥ := w183b2_two_fixSub_eq_bot hc.toBr1Base hL
  have hb_e : ∀ b ∈ B, b e₁ + b e₂ = e₁ + e₂ := by
    intro b hb
    have := heB b hb
    rwa [map_add] at this
  have heq : ∀ b ∈ B, b e₁ - e₁ = b e₂ - e₂ := by
    intro b hb
    have h0 : b e₁ - e₁ - (b e₂ - e₂) = 0 := by
      rw [show b e₁ - e₁ - (b e₂ - e₂) = (b e₁ + b e₂) - (e₁ + e₂) by
        simp only [ZModModule.sub_eq_add]
        abel]
      rw [hb_e b hb, sub_self]
    exact sub_eq_zero.mp h0
  have he₁B : e₁ ∈ fixSub B := by
    intro b hb
    have hbD : b ∈ D := hBD hb
    have h1 : b e₁ - e₁ ∈ commSpace L₁ ⊤ :=
      (commSpace L₁ ⊤).sub_mem (hinv₁ b hbD e₁ he₁) he₁
    have h2 : b e₂ - e₂ ∈ commSpace L₂ ⊤ :=
      (commSpace L₂ ⊤).sub_mem (hinv₂ b hbD e₂ he₂) he₂
    have hmem : b e₁ - e₁ ∈ commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤ :=
      ⟨h1, by rw [heq b hb]; exact h2⟩
    rw [hEinf, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have he₂B : e₂ ∈ fixSub B := by
    intro b hb
    have hbD : b ∈ D := hBD hb
    have h1 : b e₁ - e₁ ∈ commSpace L₁ ⊤ :=
      (commSpace L₁ ⊤).sub_mem (hinv₁ b hbD e₁ he₁) he₁
    have h2 : b e₂ - e₂ ∈ commSpace L₂ ⊤ :=
      (commSpace L₂ ⊤).sub_mem (hinv₂ b hbD e₂ he₂) he₂
    have hmem : b e₂ - e₂ ∈ commSpace L₁ ⊤ ⊓ commSpace L₂ ⊤ :=
      ⟨by rw [← heq b hb]; exact h1, h2⟩
    rw [hEinf, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have he₁ED : e₁ ∈ ED D := by
    by_contra h
    have hrank := w183b2_finrank_comm_le hDe hDq hBD he₁B
    have h2 := hED.rank D hD e₁ h
    have hδ := hc.delta_le D hD
    have hmi := hc.hmi
    omega
  have he₂ED : e₂ ∈ ED D := by
    by_contra h
    have hrank := w183b2_finrank_comm_le hDe hDq hBD he₂B
    have h2 := hED.rank D hD e₂ h
    have hδ := hc.delta_le D hD
    have hmi := hc.hmi
    omega
  have hVA := w183b2_two_VA_inf_fixSub hc.toBr1Base hL hD (hmem D hD) hD₁ hD₂
  have he₁fixD : e₁ ∈ fixSub D := by
    intro d hd
    have hcomm : d e₁ - e₁ ∈ commSpace D (ED D) :=
      sub_mem_commSpace (K := D) (U := ED D) hd he₁ED
    have h1 : d e₁ - e₁ ∈ VA D := hED.comm_le D hD hcomm
    have h2 : d e₁ - e₁ ∈ fixSub L₂ :=
      hE₁fix ((commSpace L₁ ⊤).sub_mem (hinv₁ d hd e₁ he₁) he₁)
    have hbot : d e₁ - e₁ ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hVA.1]; exact ⟨h1, h2⟩
    exact sub_eq_zero.mp (by simpa using hbot)
  have he₂fixD : e₂ ∈ fixSub D := by
    intro d hd
    have hcomm : d e₂ - e₂ ∈ commSpace D (ED D) :=
      sub_mem_commSpace (K := D) (U := ED D) hd he₂ED
    have h1 : d e₂ - e₂ ∈ VA D := hED.comm_le D hD hcomm
    have h2 : d e₂ - e₂ ∈ fixSub L₁ :=
      hE₂fix ((commSpace L₂ ⊤).sub_mem (hinv₂ d hd e₂ he₂) he₂)
    have hbot : d e₂ - e₂ ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hVA.2]; exact ⟨h1, h2⟩
    exact sub_eq_zero.mp (by simpa using hbot)
  exact heD (Submodule.add_mem _ he₁fixD he₂fixD)

end CFSG.LocalAnalysis.WeakClosure81

end
