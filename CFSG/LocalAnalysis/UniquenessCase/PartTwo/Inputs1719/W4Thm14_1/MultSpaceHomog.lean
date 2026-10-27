module

public import CFSG.Quasithin.Background.HPair
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem map_mul_eq_map_of_mem_centralizer {I : Subgroup W} {L : Subgroup (MulAut W)}
    {l m : MulAut W} (hl : l ∈ L) (hm : m ∈ Subgroup.centralizer (L : Set (MulAut W)))
    (hI : StableUnder L I) :
    I.map ((l * m : MulAut W).toMonoidHom) = I.map (m : MulAut W).toMonoidHom := by
  have hInv : StableUnder L (I.map (m : MulAut W).toMonoidHom) := by
    intro x hx w hw
    rw [Subgroup.mem_map] at hw ⊢
    obtain ⟨v, hv, hvw⟩ := hw
    refine ⟨x v, hI x hx v hv, ?_⟩
    rw [← hvw]
    have hcomm : x * m = m * x := Subgroup.mem_centralizer_iff.mp hm x hx
    have happly := congrFun (congrArg (fun f : MulAut W => (f : W → W)) hcomm) v
    exact happly.symm
  have hmap : (I.map (m : MulAut W).toMonoidHom).map (l : MulAut W).toMonoidHom =
      I.map (m : MulAut W).toMonoidHom := by
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_map] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact hInv l hl v hv
    · intro w hw
      rw [Subgroup.mem_map]
      exact ⟨l⁻¹ w, hInv l⁻¹ (L.inv_mem hl) w hw, by simp⟩
  have hcomp : ((l * m : MulAut W).toMonoidHom) =
      (l : MulAut W).toMonoidHom.comp (m : MulAut W).toMonoidHom := by
    ext x
    simp [MulAut.mul_apply]
  calc I.map ((l * m : MulAut W).toMonoidHom)
      = I.map ((l : MulAut W).toMonoidHom.comp (m : MulAut W).toMonoidHom) := by rw [hcomp]
    _ = (I.map (m : MulAut W).toMonoidHom).map (l : MulAut W).toMonoidHom := by
        rw [Subgroup.map_map]
    _ = I.map (m : MulAut W).toMonoidHom := hmap

private theorem mulEquiv_of_secIsoOn_bot {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) :
    ∃ e : ↥A ≃* ↥B, ∀ x ∈ X, ∀ a a' : ↥A, (a' : W) = x (a : W) → (e a' : W) = x (e a) := by
  obtain ⟨_, _, _, _, _, _, β, hβB, hβbot, hβsurj, hβcomm⟩ := h
  let β' : ↥A →* ↥B :=
    { toFun := fun a => ⟨β a, hβB a⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [map_mul] }
  have hβ'inj : Function.Injective β' := by
    intro a₁ a₂ h
    have hβeq : β a₁ = β a₂ := congrArg Subtype.val h
    have hβone : β (a₁ * a₂⁻¹) = 1 := by
      simp [map_mul, hβeq]
    have hmem : β (a₁ * a₂⁻¹) ∈ (⊥ : Subgroup W) := by
      rw [hβone]
      exact Subgroup.one_mem _
    have ha : (a₁ * a₂⁻¹ : ↥A) = 1 := by
      apply Subtype.ext
      simpa using (Subgroup.mem_bot.mp ((hβbot (a₁ * a₂⁻¹)).mp hmem))
    exact mul_inv_eq_one.mp ha
  have hβ'surj : Function.Surjective β' := by
    intro b
    obtain ⟨a, ha⟩ := hβsurj b.val b.2
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have h : β a * b.val⁻¹ = 1 := by
      simpa using (Subgroup.mem_bot.mp ha)
    exact mul_inv_eq_one.mp h
  let e : ↥A ≃* ↥B := MulEquiv.ofBijective β' ⟨hβ'inj, hβ'surj⟩
  refine ⟨e, ?_⟩
  intro x hx a a' ha'
  have hβcomm' := hβcomm x hx a a' ha'
  have hβeq : β a' = x (β a) := by
    have h : β a' * (x (β a))⁻¹ = 1 := by
      simpa using (Subgroup.mem_bot.mp hβcomm')
    exact mul_inv_eq_one.mp h
  have he' : (e a' : W) = β a' := rfl
  have he : (e a : W) = β a := rfl
  rw [he', he]
  exact hβeq

theorem exists_mul_of_mem {Y L M : Subgroup (MulAut W)} (hM : M = centGroupIn Y L)
    (hY : Y = L ⊔ M) {g : MulAut W} (hg : g ∈ Y) : ∃ l ∈ L, ∃ m ∈ M, g = l * m := by
  have hMle : M ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [hM]
    exact le_trans inf_le_right (Subgroup.centralizer_le_normalizer (L : Set (MulAut W)))
  rw [hY, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L M hMle] at hg
  obtain ⟨l, hl, m, hm, hlm⟩ := hg
  exact ⟨l, hl, m, hm, hlm.symm⟩

theorem inf_centGroupIn_eq_bot {Y L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) :
    L ⊓ centGroupIn Y L = ⊥ := by
  have hZ : Subgroup.center ↥L = ⊥ := by
    obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3
    have hmap := Subgroup.map_center_eq e
    rw [CFSG.QuasithinUnique.Setup.Family.center_GL32] at hmap
    have hinj : Function.Injective (Subgroup.map e.toMonoidHom) :=
      Subgroup.map_injective e.injective
    rw [← Subgroup.map_bot e.toMonoidHom] at hmap
    exact hinj hmap
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ L := hx.1
  have hxcent : x ∈ centGroupIn Y L := hx.2
  have hxcentL : x ∈ Subgroup.centralizer (L : Set (MulAut W)) := hxcent.2
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxcentL l l.2
  rw [hZ] at hxZ
  have hx1 : (⟨x, hxL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hxZ
  have hxeq : x = 1 := Subtype.ext_iff.mp hx1
  rw [hxeq]
  exact Subgroup.one_mem ⊥

theorem exists_mul_of_sq_eq_one {Y L M : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1)
    (hM : M = centGroupIn Y L) (hY : Y = L ⊔ M) {t : MulAut W} (ht : t ∈ Y) (ht2 : t ^ 2 = 1) :
    ∃ a ∈ L, ∃ b ∈ M, t = a * b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 := by
  obtain ⟨a, ha, b, hb, htab⟩ := exists_mul_of_mem hM hY ht
  have hb_cent : b ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM] at hb
    exact hb.2
  have hcomm : Commute a b := Subgroup.mem_centralizer_iff.mp hb_cent a ha
  have ht2' : (a * b) ^ 2 = 1 := by rw [← htab, ht2]
  have hsq : a ^ 2 * b ^ 2 = 1 := by
    rw [hcomm.mul_pow 2] at ht2'
    exact ht2'
  have ha2L : a ^ 2 ∈ L := L.pow_mem ha 2
  have hb2M : b ^ 2 ∈ M := M.pow_mem hb 2
  have ha2M : a ^ 2 ∈ M := by
    have h_eq : a ^ 2 = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [h_eq]
    exact M.inv_mem hb2M
  have ha2inf : a ^ 2 ∈ L ⊓ M := ⟨ha2L, ha2M⟩
  have hbot : L ⊓ M = ⊥ := by
    rw [hM]
    exact inf_centGroupIn_eq_bot hL3
  rw [hbot] at ha2inf
  have ha2 : a ^ 2 = 1 := Subgroup.mem_bot.mp ha2inf
  have hb2 : b ^ 2 = 1 := by
    rw [ha2, one_mul] at hsq
    exact hsq
  exact ⟨a, ha, b, hb, htab, ha2, hb2⟩

theorem isoMod_of_mem_irrSet {Y L M : Subgroup (MulAut W)} (hM : M = centGroupIn Y L)
    (hY : Y = L ⊔ M) (hfix : fixV L = ⊥) (htr : IrrSpanTrans Y L) {I J : Subgroup W}
    (hI : I ∈ irrSet L) (hJ : J ∈ irrSet L) : CFSG.Quasithin.H.Pair.IsoMod L I J := by
  obtain ⟨g, hgY, hSec⟩ := htr.2 I hI J hJ
  simp only [hfix, sup_bot_eq] at hSec
  obtain ⟨l, hl, m, hm, hglm⟩ := exists_mul_of_mem hM hY hgY
  have hm_cent : m ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM] at hm
    exact hm.2
  have hmap : I.map (g : MulAut W).toMonoidHom = I.map (m : MulAut W).toMonoidHom := by
    rw [hglm]
    exact map_mul_eq_map_of_mem_centralizer hl hm_cent
      (CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hI)
  rw [hmap] at hSec
  obtain ⟨e₁, he₁⟩ := mulEquiv_of_secIsoOn_bot hSec
  let e₂ : ↥I ≃* ↥(I.map (m : MulAut W).toMonoidHom) :=
    (m : W ≃* W).subgroupMap I
  let e : ↥I ≃* ↥J := e₂.trans e₁
  refine ⟨e, ?_⟩
  intro x hx w hw
  dsimp only [e]
  change (e₁ (e₂ ⟨x w.val, hw⟩) : W) = x (e₁ (e₂ w) : W)
  have he₂_comm : (e₂ ⟨x w.val, hw⟩ : W) = x (e₂ w : W) := by
    dsimp only [e₂]
    change (m (x w.val) : W) = x (m w.val)
    have hcomm : x * m = m * x := Subgroup.mem_centralizer_iff.mp hm_cent x hx
    have happly := congrFun (congrArg (fun f : MulAut W => (f : W → W)) hcomm) w.val
    exact happly.symm
  exact he₁ x hx (e₂ w) (e₂ ⟨x w.val, hw⟩) he₂_comm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
