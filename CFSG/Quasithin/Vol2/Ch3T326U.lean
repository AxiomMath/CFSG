module

public import CFSG.Quasithin.Vol2.Ch3T326T
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem comm_of_inner {Mp L : Subgroup (MulAut W)} {V : Subgroup W} {t z : MulAut W}
    (hMp : Mp = L ⊔ conjAutSub t L) (hinv : ∀ a ∈ Mp, ∀ v ∈ V, a v ∈ V)
    (hVU : V ≤ commSub ⊤ L) (hUfix : ∀ u ∈ commSub ⊤ L, ∀ g ∈ conjAutSub t L, g u = u)
    (hzU : ∀ u ∈ commSub ⊤ L, z u ∈ commSub ⊤ L) (hzc : ∀ a ∈ L, z * a = a * z) :
    ∀ a ∈ Mp, ∀ v ∈ V, z (a v) = a (z v) := by
  intro a ha
  rw [hMp, Subgroup.sup_eq_closure] at ha
  have hMp' : Subgroup.closure ((L : Set (MulAut W)) ∪ conjAutSub t L) = Mp := by
    rw [hMp, Subgroup.sup_eq_closure]
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    intro v hv
    rcases ha with ha | ha
    · rw [← MulAut.mul_apply, hzc a ha, MulAut.mul_apply]
    · rw [hUfix v (hVU hv) a ha, hUfix (z v) (hzU v (hVU hv)) a ha]
  | one => intro v _; rfl
  | mul a b ha hb iha ihb =>
    intro v hv
    have hb' : b ∈ Mp := hMp' ▸ hb
    rw [MulAut.mul_apply, MulAut.mul_apply, iha (b v) (hinv b hb' v hv), ihb v hv]
  | inv a ha iha =>
    intro v hv
    have ha' : a ∈ Mp := hMp' ▸ ha
    have h1 := iha (a⁻¹ v) (hinv _ (Mp.inv_mem ha') v hv)
    rw [MulAut.apply_inv_self] at h1
    rw [h1, MulAut.inv_apply_self]

theorem map_eq_self_of_inner [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (hD : D3Std M Mp T L V) (horb : orbSup T V = ⊤)
    (hMp : Mp = L ⊔ conjAutSub t L) (hVU : V ≤ commSub ⊤ L)
    (hUfix : ∀ u ∈ commSub ⊤ L, ∀ g ∈ conjAutSub t L, g u = u) {n z a : MulAut W}
    (hn : n ∈ T) (hz : z ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hzU : ∀ u ∈ commSub ⊤ L, z u ∈ commSub ⊤ L) (hzc : ∀ b ∈ L, z * b = b * z)
    (ha : a ∈ L) (hnaz : n = a * z) : V.map n.toMonoidHom = V := by
  have hinv : ∀ b ∈ Mp, ∀ v ∈ V, b v ∈ V := fun b hb v hv => hD.hyp.irr.2.1 ⟨b, hb⟩ v hv
  have hcomm := comm_of_inner hMp hinv hVU hUfix hzU hzc
  have haMp : a ∈ Mp := by
    rw [hMp]
    exact Subgroup.mem_sup_left ha
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := fun s hs =>
    hD.hyp.Mp_normal (hD.hyp.sylow.1 hs)
  have hirr := hD.irrT
  rw [horb] at hirr
  refine map_eq_self_of_comm hTMp hirr hn hz hcomm ?_
  have hle : V.map n.toMonoidHom ≤ V.map z.toMonoidHom := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨a v, hinv a haMp v hv, ?_⟩
    show z (a v) = n v
    rw [hcomm a haMp v hv, hnaz, MulAut.mul_apply]
  have hcard : Nat.card ↥(V.map z.toMonoidHom) = Nat.card ↥(V.map n.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := n.toMonoidHom) n.injective,
      Subgroup.card_map_of_injective (f := z.toMonoidHom) z.injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard.le

end CFSG.Quasithin.H13.T326
