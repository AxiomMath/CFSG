module

public import CFSG.Quasithin.Background.F918Z8Plumb
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.F918Z8Ex1
public import CFSG.Quasithin.Background.F918Z8Ex2
public import CFSG.Quasithin.Background.F918Z8Ex3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

section Helpers

variable {W : Type} [CommGroup W]

omit [CommGroup W] in
theorem d321x_le_stabSub_bot {W : Type} [CommGroup W] (X : Subgroup (MulAut W)) :
    X ≤ stabSub (⊥ : Subgroup W) := fun g _ u => by simp [Subgroup.mem_bot]

theorem d321x_rkIdx_anti_D [Finite W] {A : Subgroup (MulAut W)} {N D D' : Subgroup W}
    (hDD' : D ≤ D') (hD'N : D' ≤ N) (hAN : A ≤ stabSub N) (hAD : A ≤ stabSub D)
    (hAD' : A ≤ stabSub D') :
    rkIdx (fixV (autSec A N D')) ≤ rkIdx (fixV (autSec A N D)) := by
  have h1 := d321d_rkIdx_add_rk_commModSub (hDD'.trans hD'N) hAN hAD
  have h2 := d321d_rkIdx_add_rk_commModSub hD'N hAN hAD'
  have h3 : rk (commModSub N A D) ≤ rk (commModSub N A D') :=
    rk_mono fun n hn => ⟨hn.1, fun g hg => hDD' (hn.2 g hg)⟩
  omega

theorem d321x_split_U [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {U U' C : Subgroup W} (hint : (U ⊔ C) ⊓ (U' ⊔ C) ≤ C)
    (hAU : A ≤ stabSub U) (hAU' : A ≤ stabSub U') (hAC : A ≤ stabSub C) :
    rkIdx (fixV (autSec A U ⊥)) + rkIdx (fixV (autSec A U' (U' ⊓ C))) ≤ rkIdx (fixV A) := by
  have hUU' : A ≤ stabSub (U ⊔ U') := d321d_stabSub_sup hAU hAU'
  have h1 := B5.rkIdx_chain hexp (bot_le : (⊥ : Subgroup W) ≤ U) (le_refl U)
    (le_sup_left : U ≤ U ⊔ U') hAU hUU' hAU
  have h2 := d321d_rkIdx_fixV_autSec_sup hAU' hAU
  rw [sup_comm U' U] at h2
  have hle : U' ⊓ U ≤ U' ⊓ C := fun x hx => ⟨hx.1, hint ⟨Subgroup.mem_sup_left hx.2,
    Subgroup.mem_sup_left hx.1⟩⟩
  have h3 := d321x_rkIdx_anti_D hle (inf_le_left : U' ⊓ C ≤ U') hAU'
    (d321d_stabSub_inf hAU' hAU) (d321d_stabSub_inf hAU' hAC)
  omega

end Helpers


section Ctx

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d321x_center_trivial (hL38 : D3L38)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L) :
    ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1 := by
  obtain ⟨hA38, -, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hD := hstd.hyp
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hD.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  intro z hz hc
  by_contra hz1
  have hcen : Subgroup.center ↥L = ⊤ := by
    rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exfalso
      have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hc g g.2).symm
      rw [h, Subgroup.mem_bot] at hmem
      exact hz1 (congrArg Subtype.val hmem)
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  have ha : a ∈ Subgroup.center ↥L := by rw [hcen]; trivial
  exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem d321x_inn (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hVT : commSub (orbSup T V) L = V) (hpsl : IsPSL 3 2 1 ↥L)
    (hds : DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp)
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4) :
    ∀ a ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      ∃ b ∈ L, ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹ := by
  have hD := hstd.hyp
  have hexp := hD.exp
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.sylow.1.trans hD.Mp_normal
  have hLU : L ≤ stabSub (commV L) := d321p_L_stab_U hstd
  have hLZ : L ≤ stabSub (commV L ⊓ fixV Mp) := d321p_L_stab_Z hstd
  have hf := d321_faithful_tilde hL38 hstd htT htL hMp htriv
  have hVU : V ≤ commV L := d321h_le_commV hstd hMp htriv
  obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hD.irr
  have hLMp : L ≤ Mp := d321p_le_Mp hMp
  refine d321x_inner hexp (S := T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (V := V)
    inf_le_left hLU hLZ hf hpsl hds hVU (fun l hl v hv => hinv l (hLMp hl) v hv) ?_ ?_ ?_ ?_ ?_
    (d321_stab_V hL38 hstd htT htL hMp hVT)
  · intro h
    have h1 : V ≤ fixV Mp := fun v hv => (h hv).2
    exact absurd (inf_eq_left.2 h1) hlt.ne
  · intro X hXV hXL hZX
    have h1 : L ≤ stabSub X := Z391.le_stabSub_iff.2 hXL
    have h2 : conjAutSub t L ≤ stabSub X := Z391.le_stabSub_iff.2 fun g hg w hw => by
      rw [htriv w (hXV hw) g hg]; exact hw
    have h3 : Mp ≤ stabSub X := by rw [hMp]; exact sup_le h1 h2
    have hXMp := Z391.le_stabSub_iff.1 h3
    have e : V ⊓ (commV L ⊓ fixV Mp) = V ⊓ fixV Mp := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hVU h.1, h.2⟩⟩
    rw [e] at hZX ⊢
    rcases hirr X (fun x hx w hw => hXMp x hx w hw) hZX hXV with h | h
    · left; exact h
    · right; exact h
  · exact inf_le_right
  · exact inf_le_right.trans (d321p_normalizer_le_stabSub_commV L)
  · exact d321p_le_stabSub_inf (inf_le_right.trans (d321p_normalizer_le_stabSub_commV L))
      (d321d_le_stabSub_fixV (inf_le_left.trans hTn))


theorem d321x_n_lower (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hVT : commSub (orbSup T V) L = V) (hpsl : IsPSL 3 2 1 ↥L)
    (hds : DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp)
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (hZ : commV L ⊓ fixV Mp ≠ ⊥) {a : MulAut W} (haT : a ∈ T)
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut W))) (ha2 : a * a = 1)
    (haC : ¬ ∀ l ∈ L, a * l = l * a) :
    5 ≤ rkIdx (fixV (autSec (Subgroup.zpowers a) (commV L) ⊥)) ∧
      4 ≤ rkIdx (fixV (autSec (Subgroup.zpowers a) (commV L) (commV L ⊓ fixV Mp))) := by
  have hD := hstd.hyp
  have hexp := hD.exp
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.sylow.1.trans hD.Mp_normal
  obtain ⟨b, hbL, hb⟩ := d321x_inn hL38 hstd htT htL hMp htriv hVT hpsl hds a ⟨haT, haN⟩
  have hcen := d321x_center_trivial hL38 hstd htT htL hMp
  have hc : ∀ l ∈ L, b⁻¹ * a * l = l * (b⁻¹ * a) := by
    intro l hl
    have h1 := hb l hl
    calc b⁻¹ * a * l = b⁻¹ * (a * l * a⁻¹) * a := by group
      _ = b⁻¹ * (b * l * b⁻¹) * a := by rw [h1]
      _ = l * (b⁻¹ * a) := by group
  have hb1 : b ≠ 1 := by
    intro h
    apply haC
    intro l hl
    have h1 := hb l hl
    rw [h] at h1
    calc a * l = (a * l * a⁻¹) * a := by group
      _ = l * a := by rw [h1]; group
  have hbb : b * b = 1 := by
    have hcb : b⁻¹ * a * b = b * (b⁻¹ * a) := hc b hbL
    have h3 : (b * b) * ((b⁻¹ * a) * (b⁻¹ * a)) = 1 := by
      calc (b * b) * ((b⁻¹ * a) * (b⁻¹ * a)) = b * (b * (b⁻¹ * a)) * (b⁻¹ * a) := by group
        _ = b * ((b⁻¹ * a) * b) * (b⁻¹ * a) := by rw [hcb]
        _ = a * a := by group
        _ = 1 := ha2
    apply hcen _ (L.mul_mem hbL hbL)
    intro l hl
    have hcl : Commute (b⁻¹ * a) l := hc l hl
    have hd : Commute ((b⁻¹ * a) * (b⁻¹ * a)) l := hcl.mul_left hcl
    have e : b * b = ((b⁻¹ * a) * (b⁻¹ * a))⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [e]
    exact (hd.inv_left).eq
  have e1 : b * (b⁻¹ * a) = a := by group
  have hperfL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hD.quasi.1
    exact Subgroup.commutator_eq_self
  have hLU : L ≤ stabSub (commV L) := d321p_L_stab_U hstd
  have hLZ : L ≤ stabSub (commV L ⊓ fixV Mp) := d321p_L_stab_Z hstd
  have hf := d321_faithful_tilde hL38 hstd htT htL hMp htriv
  have haU : a ∈ stabSub (commV L) := d321p_normalizer_le_stabSub_commV L haN
  have haZ : a ∈ stabSub (commV L ⊓ fixV Mp) :=
    d321p_le_stabSub_inf (X := T ⊓ Subgroup.normalizer (L : Set (MulAut W)))
      (fun g hg => d321p_normalizer_le_stabSub_commV L hg.2)
      (fun g hg => d321d_le_stabSub_fixV hTn hg.1) ⟨haT, haN⟩
  have hcU : b⁻¹ * a ∈ stabSub (commV L) :=
    (stabSub (commV L)).mul_mem ((stabSub (commV L)).inv_mem (hLU hbL)) haU
  have hcZ : b⁻¹ * a ∈ stabSub (commV L ⊓ fixV Mp) :=
    (stabSub (commV L ⊓ fixV Mp)).mul_mem ((stabSub (commV L ⊓ fixV Mp)).inv_mem (hLZ hbL)) haZ
  have hbotst : ∀ g : MulAut W, g ∈ stabSub (⊥ : Subgroup W) := fun g u => by
    simp [Subgroup.mem_bot]
  have hfbot : L ⊓ centSec (commV L) ⊥ = ⊥ := by
    rw [eq_bot_iff, ← hf]
    intro g hg
    refine ⟨hg.1, hg.2.1, fun w hw => ?_⟩
    have := hg.2.2 w hw
    rw [Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  have hperf : commSub (commV L) L = commV L := B5.commSub_commV_eq hperfL
  have g1 := d321x_gen_sec hexp (L := L) (U := commV L) (Z := ⊥) bot_le hLU
    (fun g _ => hbotst g) hfbot hpsl (by rw [sup_bot_eq]; exact hperf) hbL hb1 hbb hc hcU
    (hbotst _)
  have g2 := d321x_gen_sec hexp (L := L) (U := commV L) (Z := commV L ⊓ fixV Mp) inf_le_left
    hLU hLZ hf hpsl (by rw [hperf]; exact sup_eq_left.2 inf_le_left) hbL hb1 hbb hc hcU hcZ
  rw [e1] at g1 g2
  have r12 := d321x_rk_sec hds
  have r1 := B5.rk_sec_add (bot_le : (⊥ : Subgroup W) ≤ commV L)
  have r2 := B5.rk_sec_add (inf_le_left : commV L ⊓ fixV Mp ≤ commV L)
  have r3 : 0 < rk ↥(commV L ⊓ fixV Mp) :=
    Nat.pos_of_ne_zero fun h => hZ ((rk_eq_zero_iff hexp).1 h)
  rw [rk_bot] at r1
  constructor <;> omega


theorem d321x_n_lower_t (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hVT : commSub (orbSup T V) L = V) (hpsl : IsPSL 3 2 1 ↥L)
    (hds : DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp)
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    (hZ : commV L ⊓ fixV Mp ≠ ⊥) {a : MulAut W} (haT : a ∈ T)
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut W))) (ha2 : a * a = 1)
    (haC : ¬ ∀ l ∈ conjAutSub t L, a * l = l * a) :
    5 ≤ rkIdx (fixV (autSec (Subgroup.zpowers a) ((commV L).map t.toMonoidHom) ⊥)) ∧
      4 ≤ rkIdx (fixV (autSec (Subgroup.zpowers a) ((commV L).map t.toMonoidHom)
        (((commV L).map t.toMonoidHom) ⊓ fixV Mp))) := by
  have hD := hstd.hyp
  have hTM : T ≤ M := hD.sylow.1
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hTM.trans hD.Mp_normal
  have htM : t ∈ M := hTM htT
  have hperm := d321d_perm hL38 hstd htT htL hMp
  have ha'T : t⁻¹ * a * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem htT) haT) htT
  have haLt : a ∈ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    d321a_mem_normalizer_iff.mpr (d321d_normalizes_conj hperm htM htL (hTM haT)
      (d321a_mem_normalizer_iff.mp haN))
  have ha'N : t⁻¹ * a * t ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [d321a_mem_normalizer_iff, d321a_conjAutSub_mul, d321a_conjAutSub_mul,
      d321a_mem_normalizer_iff.mp haLt, conjAutSub_inv_conjAutSub]
  have ha'2 : (t⁻¹ * a * t) * (t⁻¹ * a * t) = 1 := by
    calc (t⁻¹ * a * t) * (t⁻¹ * a * t) = t⁻¹ * (a * a) * t := by group
      _ = 1 := by rw [ha2]; group
  have ha'C : ¬ ∀ l ∈ L, (t⁻¹ * a * t) * l = l * (t⁻¹ * a * t) := by
    intro h
    apply haC
    intro l' hl'
    have hl : t⁻¹ * l' * t ∈ L := mem_conjAutSub_iff.1 hl'
    calc a * l' = t * ((t⁻¹ * a * t) * (t⁻¹ * l' * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * l' * t) * (t⁻¹ * a * t)) * t⁻¹ := by rw [h _ hl]
      _ = l' * a := by group
  have key := d321x_n_lower hL38 hstd htT htL hMp htriv hVT hpsl hds hZ ha'T ha'N ha'2 ha'C
  have hbotst : ∀ g : MulAut W, g ∈ stabSub (⊥ : Subgroup W) := fun g u => by
    simp [Subgroup.mem_bot]
  have hz : conjAutSub t (Subgroup.zpowers (t⁻¹ * a * t)) = Subgroup.zpowers a := by
    unfold conjAutSub
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply]
    group
  have hEU : Subgroup.zpowers (t⁻¹ * a * t) ≤ stabSub (commV L) :=
    Subgroup.zpowers_le.2 (d321p_normalizer_le_stabSub_commV L ha'N)
  have ha'Z : t⁻¹ * a * t ∈ stabSub (commV L ⊓ fixV Mp) :=
    d321p_le_stabSub_inf (X := T ⊓ Subgroup.normalizer (L : Set (MulAut W)))
      (fun g hg => d321p_normalizer_le_stabSub_commV L hg.2)
      (fun g hg => d321d_le_stabSub_fixV hTn hg.1) ⟨ha'T, ha'N⟩
  have hEZ : Subgroup.zpowers (t⁻¹ * a * t) ≤ stabSub (commV L ⊓ fixV Mp) :=
    Subgroup.zpowers_le.2 ha'Z
  have hU1 := d321d_rkIdx_fixV_autSec_conj t (E := Subgroup.zpowers (t⁻¹ * a * t))
    (N := commV L) (D := ⊥) bot_le hEU (fun g _ => hbotst g)
  have hU2 := d321d_rkIdx_fixV_autSec_conj t (E := Subgroup.zpowers (t⁻¹ * a * t))
    (N := commV L) (D := commV L ⊓ fixV Mp) inf_le_left hEU hEZ
  rw [hz, Subgroup.map_bot] at hU1
  rw [hz, Subgroup.map_inf _ _ _ t.injective, d321d_map_fixV (hTn htT)] at hU2
  rw [hU1, hU2]
  exact key

theorem d321x_rank_four (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hVT : commSub (orbSup T V) L = V) (hpsl : IsPSL 3 2 1 ↥L)
    (hds : DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp)
      (FFModel.nat (StatedSL 3 (ZMod 2))) 4)
    {B : Subgroup (MulAut W)} (hBT : B ≤ T)
    (hBN : B ≤ Subgroup.normalizer (L : Set (MulAut W))) (hB : IsElemAbelian2 B)
    (hBf : ∀ b ∈ B, (∀ x ∈ Mp, b * x = x * b) → b = 1) :
    rk ↥B ≤ 4 ∧ ((∀ b ∈ B, ∀ l ∈ L, b * l = l * b) → rk ↥B ≤ 2) ∧
      ((∀ b ∈ B, ∀ l ∈ conjAutSub t L, b * l = l * b) → rk ↥B ≤ 2) ∧
      ((∀ b ∈ B, ∀ l ∈ L, b * l = l * b) → (∀ b ∈ B, ∀ l ∈ conjAutSub t L, b * l = l * b) →
        B = ⊥) := by
  have hD := hstd.hyp
  have hTM : T ≤ M := hD.sylow.1
  have htM : t ∈ M := hTM htT
  have hperm := d321d_perm hL38 hstd htT htL hMp
  have hinn := d321x_inn hL38 hstd htT htL hMp htriv hVT hpsl hds
  have hBLt : B ≤ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    fun g hg => d321a_mem_normalizer_iff.mpr (d321d_normalizes_conj hperm htM htL
      (hTM (hBT hg)) (d321a_mem_normalizer_iff.mp (hBN hg)))
  have hpsl' : IsPSL 3 2 1 ↥(conjAutSub t L) :=
    isPSL_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective) hpsl
  have hinn_B : ∀ a ∈ B, ∃ b ∈ L, ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹ :=
    fun a ha => hinn a ⟨hBT ha, hBN ha⟩
  have hinn' : ∀ a ∈ B, ∃ b ∈ conjAutSub t L, ∀ l ∈ conjAutSub t L,
      a * l * a⁻¹ = b * l * b⁻¹ := by
    intro a ha
    have ha'T : t⁻¹ * a * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem htT) (hBT ha)) htT
    have ha'N : t⁻¹ * a * t ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [d321a_mem_normalizer_iff, d321a_conjAutSub_mul, d321a_conjAutSub_mul,
        d321a_mem_normalizer_iff.mp (hBLt ha), conjAutSub_inv_conjAutSub]
    obtain ⟨b, hbL, hb⟩ := hinn _ ⟨ha'T, ha'N⟩
    refine ⟨t * b * t⁻¹, mem_conjAutSub_iff.2 ?_, fun l hl => ?_⟩
    · have e : t⁻¹ * (t * b * t⁻¹) * t = b := by group
      rw [e]; exact hbL
    · have hl' : t⁻¹ * l * t ∈ L := mem_conjAutSub_iff.1 hl
      have h1 := hb _ hl'
      calc a * l * a⁻¹ = t * ((t⁻¹ * a * t) * (t⁻¹ * l * t) * (t⁻¹ * a * t)⁻¹) * t⁻¹ := by group
        _ = t * (b * (t⁻¹ * l * t) * b⁻¹) * t⁻¹ := by rw [h1]
        _ = (t * b * t⁻¹) * l * (t * b * t⁻¹)⁻¹ := by group
  have r1 := d321x_rank_cent hpsl hBN hB hinn_B
  have r2 := d321x_rank_cent hpsl' hBLt hB hinn'
  have hKey : ∀ x ∈ B, x ∈ Subgroup.centralizer (L : Set (MulAut W)) →
      x ∈ Subgroup.centralizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) →
      x = 1 := by
    intro x hxB hx1 hx2
    apply hBf x hxB
    have hLK : L ≤ Subgroup.centralizer ({x} : Set (MulAut W)) := fun l hl => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.1 hx1 l hl).symm
    have hLtK : conjAutSub t L ≤ Subgroup.centralizer ({x} : Set (MulAut W)) := fun l hl => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.1 hx2 l hl).symm
    have hKMp : Mp ≤ Subgroup.centralizer ({x} : Set (MulAut W)) := by
      rw [hMp]; exact sup_le hLK hLtK
    intro y hy
    exact Subgroup.mem_centralizer_iff.1 (hKMp hy) x (Set.mem_singleton x)
  set R := B ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hR
  set R' := B ⊓ Subgroup.centralizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W))
    with hR'
  have hRR : R ⊓ R' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hKey x hx.1.1 hx.1.2 hx.2.2
  have h3 := B2F.rk_sup_add_rk_inf_of_commute (A := R) (B := R')
    (fun a ha b hb => hB.1 a ha.1 b hb.1)
  rw [hRR, rk_bot] at h3
  have h4 : rk ↥(R ⊔ R') ≤ rk ↥B := rk_mono (sup_le inf_le_left inf_le_left)
  refine ⟨by omega, fun hc => ?_, fun hc => ?_, fun hc hc' => ?_⟩
  · have hRB : R = B := inf_eq_left.2 fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (hc b hb l hl).symm
    have h5 : rk ↥R = rk ↥B := by rw [hRB]
    omega
  · have hRB : R' = B := inf_eq_left.2 fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (hc b hb l hl).symm
    have h5 : rk ↥R' = rk ↥B := by rw [hRB]
    omega
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hKey x hx (Subgroup.mem_centralizer_iff.2 fun l hl => (hc x hx l hl).symm)
      (Subgroup.mem_centralizer_iff.2 fun l hl => (hc' x hx l hl).symm)

end Ctx


theorem d321Exact_of_inputs (hL38 : D3L38) : D321Exact := by
  intro W _ _ M Mp T L V t A hstd htT htL hMp hqM hA htriv hlt hVT hqV htop hpsl hds
  by_contra hZ
  have hD := hstd.hyp
  have hexp := hD.exp
  have hTM : T ≤ M := hD.sylow.1
  have htM : t ∈ M := hTM htT
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hTM.trans hD.Mp_normal
  have hAM : A ≤ M := hA.le.trans hTM
  have hperm := d321d_perm hL38 hstd htT htL hMp
  obtain ⟨hsplit, -⟩ := d321_struct hL38 hstd htT htL hMp htriv
  have hrA : 0 < rk ↥A := hA.elem.rk_pos hA.ne
  have hrat : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h := hA.rat
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rw [div_le_iff₀ hpos] at h
    exact_mod_cast h
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hA.elem.2 a ha
  by_cases hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))
  ·
    obtain ⟨U', hU'⟩ : ∃ U' : Subgroup W, U' = (commV L).map t.toMonoidHom := ⟨_, rfl⟩
    rw [← hU'] at hsplit
    have hALt : A ≤ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
      fun g hg => d321a_mem_normalizer_iff.mpr (d321d_normalizes_conj hperm htM htL (hAM hg)
        (d321a_mem_normalizer_iff.mp (hAL hg)))
    have hAU : A ≤ stabSub (commV L) := d321d_le_stabSub_commV hAL
    have hAU' : A ≤ stabSub U' := by
      have h := d321d_le_stabSub_commV hALt
      rwa [d321b_commV_conjAutSub, ← hU'] at h
    have hAC : A ≤ stabSub (fixV Mp) := d321d_le_stabSub_fixV (hA.le.trans hTn)
    have hAZ : A ≤ stabSub (commV L ⊓ fixV Mp) := d321d_stabSub_inf hAU hAC
    have hAZ' : A ≤ stabSub (U' ⊓ fixV Mp) := d321d_stabSub_inf hAU' hAC
    have hI := d321x_split_U hexp hsplit.2 hAU hAU' hAC
    have hsplit2 : (U' ⊔ fixV Mp) ⊓ (commV L ⊔ fixV Mp) ≤ fixV Mp := by
      rw [inf_comm]; exact hsplit.2
    have hII := d321x_split_U hexp hsplit2 hAU' hAU hAC
    obtain ⟨rk4, rkL, rkLt, rkBot⟩ := d321x_rank_four hL38 hstd htT htL hMp htriv hVT hpsl hds
      hA.le hAL hA.elem hA.faithMp
    have hbot : A ≤ stabSub (⊥ : Subgroup W) := d321x_le_stabSub_bot A
    have mono : ∀ (a : MulAut W), a ∈ A → ∀ {N D : Subgroup W}, D ≤ N → A ≤ stabSub N →
        A ≤ stabSub D → rkIdx (fixV (autSec (Subgroup.zpowers a) N D)) ≤
          rkIdx (fixV (autSec A N D)) := fun a ha N D hDN hAN hAD =>
      d321d_rkIdx_fixV_autSec_mono (Subgroup.zpowers_le.2 ha) hDN hAN hAD
    by_cases h1 : ∀ b ∈ A, ∀ l ∈ L, b * l = l * b
    · by_cases h2 : ∀ b ∈ A, ∀ l ∈ conjAutSub t L, b * l = l * b
      · exact hA.ne (rkBot h1 h2)
      · push Not at h2
        obtain ⟨a, haA, l, hl, hal⟩ := h2
        have key := d321x_n_lower_t hL38 hstd htT htL hMp htriv hVT hpsl hds hZ (hA.le haA)
          (hAL haA) (hA2 a haA) (fun h => hal (h l hl))
        rw [← hU'] at key
        have hm := mono a haA (bot_le : (⊥ : Subgroup W) ≤ U') hAU' hbot
        have := rkL h1
        omega
    · push Not at h1
      obtain ⟨a, haA, l, hl, hal⟩ := h1
      have key1 := d321x_n_lower hL38 hstd htT htL hMp htriv hVT hpsl hds hZ (hA.le haA)
        (hAL haA) (hA2 a haA) (fun h => hal (h l hl))
      have hm1 := mono a haA (bot_le : (⊥ : Subgroup W) ≤ commV L) hAU hbot
      by_cases h2 : ∀ b ∈ A, ∀ l ∈ conjAutSub t L, b * l = l * b
      · have := rkLt h2
        omega
      · push Not at h2
        obtain ⟨a', ha'A, l', hl', hal'⟩ := h2
        have key2 := d321x_n_lower_t hL38 hstd htT htL hMp htriv hVT hpsl hds hZ (hA.le ha'A)
          (hAL ha'A) (hA2 a' ha'A) (fun h => hal' (h l' hl'))
        rw [← hU'] at key2
        have hm2 := mono a' ha'A (inf_le_left : U' ⊓ fixV Mp ≤ U') hAU' hAZ'
        omega
  ·
    obtain ⟨a, haA, haL⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (L : Set (MulAut W)) := by
      by_contra hcon
      push Not at hcon
      exact hAL fun g hg => hcon g hg
    have haconj : conjAutSub a L = conjAutSub t L :=
      (hperm a (hAM haA)).resolve_left fun h => haL (d321a_mem_normalizer_iff.mpr h)
    obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Subgroup (MulAut W),
        A₀ = A ⊓ Subgroup.normalizer (L : Set (MulAut W)) := ⟨_, rfl⟩
    have hmem : ∀ g, g ∈ A₀ ↔ g ∈ A ∧ g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      fun g => by rw [hA₀]; exact Subgroup.mem_inf
    have hA₀A : A₀ ≤ A := fun g hg => ((hmem g).mp hg).1
    have hA₀N : A₀ ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun g hg => ((hmem g).mp hg).2
    have haa : a * a = 1 := hA2 a haA
    have hsplitA : ∀ g ∈ A, g ∈ A₀ ∨ a⁻¹ * g ∈ A₀ := by
      intro g hg
      by_cases hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))
      · exact Or.inl ((hmem g).mpr ⟨hg, hgL⟩)
      · right
        have hgconj : conjAutSub g L = conjAutSub t L :=
          (hperm g (hAM hg)).resolve_left fun h => hgL (d321a_mem_normalizer_iff.mpr h)
        refine (hmem _).mpr ⟨A.mul_mem (A.inv_mem haA) hg, d321a_mem_normalizer_iff.mpr ?_⟩
        rw [d321a_conjAutSub_mul, hgconj, ← haconj, conjAutSub_inv_conjAutSub]
    have hrkA : rk ↥A ≤ rk ↥A₀ + 1 := d321d_rk_le_rk_add_one hA.elem hA₀A hsplitA haA
    have h4 := (d321x_rank_four hL38 hstd htT htL hMp htriv hVT hpsl hds (B := A₀)
      (hA₀A.trans hA.le) hA₀N (d321d_isElemAbelian2_mono hA.elem hA₀A)
      (fun b hb h => hA.faithMp b (hA₀A hb) h)).1
    have hAC : (⊥ : Subgroup (MulAut W)) ≤ stabSub (fixV Mp) := bot_le
    have haC : (fixV Mp).map a.toMonoidHom = fixV Mp := d321d_map_fixV (hTn (hA.le haA))
    have hUa : (commV L).map a.toMonoidHom = (commV L).map t.toMonoidHom := by
      have h1 := d321b_commV_conjAutSub a L
      rw [haconj, d321b_commV_conjAutSub] at h1
      exact h1.symm
    have hsumU : commV L ⊔ (commV L).map a.toMonoidHom ⊔ fixV Mp = ⊤ := by
      rw [hUa]
      exact hsplit.1.symm
    have hintU : (commV L ⊔ fixV Mp) ⊓ ((commV L).map a.toMonoidHom ⊔ fixV Mp) ≤ fixV Mp := by
      rw [hUa]
      exact hsplit.2
    have hcount := d321d_swap_count (A₀ := ⊥) haa
      (fun g hg => by rw [Subgroup.mem_bot] at hg; subst hg; simp) bot_le bot_le haC hsumU hintU
    rw [bot_sup_eq] at hcount
    have hfa : fixV A ≤ fixV (Subgroup.zpowers a) := fixV_anti (Subgroup.zpowers_le.2 haA)
    have hidx := rkIdx_anti hfa
    have r12 := d321x_rk_sec hds
    omega


end CFSG.Quasithin
