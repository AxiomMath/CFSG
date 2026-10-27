module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65WeakClosureGeneric
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardG2General
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem conjugate_le_sup_pCoreOf_of_sylowCenterWeaklyClosed {G : Type} [Group G] [Finite G]
    {D : Data G} {L Q Z : Subgroup G}
    (hY : SylowCenterWeaklyClosed (Bar2 L))
    (hLMle : L ≤ D.M) (hLM : (L.subgroupOf D.M).Normal)
    (hZQ : Z ≤ Q) (hZcentQ : Z ≤ Subgroup.centralizer (Q : Set G)) (hZcard : Nat.card Z = 3)
    (hQL : Q ≤ L) (hQsyl : ∃ S : Sylow 3 ↥L, (S : Subgroup ↥L) = Q.subgroupOf L)
    (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hQZ : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    {m : G} (hm : m ∈ D.M) (hmZ : CFSG.conjugate Z m ≤ Subgroup.normalizer (Z : Set G)) :
    CFSG.conjugate Z m ≤ Z ⊔ CFSG.Open.pCoreOf 2 L := by
  classical
  have hZL : Z ≤ L := hZQ.trans hQL
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLMle).mp hLM
  have hmN : m ∈ Subgroup.normalizer (L : Set G) := hMN hm
  have hmN' : m⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hmN
  let mkL : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let f : ↥Q →* Bar2 L := mkL.comp (Subgroup.inclusion hQL)
  have hf : Function.Injective f := injective_comp_subgroupOf_mk' hQL hQO2
  have hfrange : f.range = (Q.subgroupOf L).map mkL := range_comp_subgroupOf_mk' hQL
  obtain ⟨Pb, hPb⟩ := exists_sylow_map_subgroupOf_mk' hQsyl
  have hPb' : (Pb : Subgroup (Bar2 L)) = f.range := hPb.trans hfrange.symm
  let Zb : Subgroup (Bar2 L) := (Z.subgroupOf L).map mkL
  have hmap' : (Z.subgroupOf Q).map (Subgroup.inclusion hQL) = Z.subgroupOf L := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨(x : G), hZQ hx⟩, hx, Subtype.ext rfl⟩
  have hmap : (Z.subgroupOf Q).map f = Zb := by
    show (Z.subgroupOf Q).map (mkL.comp (Subgroup.inclusion hQL)) =
      (Z.subgroupOf L).map mkL
    rw [← Subgroup.map_map, hmap']
  have hZbcard : Nat.card Zb = 3 := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
    rw [← Subgroup.card_subtype Q (Z.subgroupOf Q), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hZQ]
    exact hZcard
  have hZbPb : Zb ≤ (Pb : Subgroup (Bar2 L)) := by
    rw [hPb]
    exact Subgroup.map_mono (fun x hx => hZQ hx)
  have hZbc : Zb ≤ Subgroup.centralizer ((Pb : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    intro zb hzb
    rw [Subgroup.mem_centralizer_iff]
    intro pb hpb
    rw [hPb] at hpb
    obtain ⟨zbL, hzbL, rfl⟩ := Subgroup.mem_map.mp hzb
    obtain ⟨qL, hqL, rfl⟩ := Subgroup.mem_map.mp hpb
    show mkL qL * mkL zbL = mkL zbL * mkL qL
    rw [← map_mul, ← map_mul]
    exact congrArg mkL (Subtype.ext <|
      (Subgroup.mem_centralizer_iff.mp (hZcentQ hzbL)) (qL : G) hqL)
  have hQZb : Nat.card ((Subgroup.center ↥(Pb : Subgroup (Bar2 L))).map
      (Pb : Subgroup (Bar2 L)).subtype) = 3 := by
    have h1 : Nat.card ((Subgroup.center ↥Q).map f) = 3 := by
      calc Nat.card ((Subgroup.center ↥Q).map f)
          = Nat.card (Subgroup.center ↥Q) := Subgroup.card_map_of_injective hf
        _ = Nat.card ((Subgroup.center ↥Q).map Q.subtype) :=
              (Subgroup.card_map_of_injective (f := Q.subtype) Q.subtype_injective).symm
        _ = 3 := hQZ
    have h2 := card_center_map_eq_of_injective f hf
    rw [h1, ← hPb'] at h2
    exact h2
  let φ : MulAut (Bar2 L) := UC6S846.rhoL L ⟨m⁻¹, hmN'⟩
  have hφ : Zb.map φ.toMonoidHom ≤ Subgroup.normalizer (Zb : Set (Bar2 L)) := by
    rw [Subgroup.le_normalizer_iff]
    intro w hw z' hz'
    obtain ⟨wz, hwz, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨wL, hwL, rfl⟩ := Subgroup.mem_map.mp hwz
    obtain ⟨zL, hzL, rfl⟩ := Subgroup.mem_map.mp hz'
    have hphiw : φ (mkL wL) = mkL (Subgroup.normalizerMonoidHom L ⟨m⁻¹, hmN'⟩ wL) :=
      UC6S846.rhoL_mk L ⟨m⁻¹, hmN'⟩ wL
    change φ (mkL wL) * mkL zL * (φ (mkL wL))⁻¹ ∈ Zb
    rw [hphiw]
    rw [← map_mul, ← map_inv, ← map_mul]
    refine Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom L ⟨m⁻¹, hmN'⟩ wL * zL *
      (Subgroup.normalizerMonoidHom L ⟨m⁻¹, hmN'⟩ wL)⁻¹, ?_, rfl⟩
    have hnorm : (MulAut.conj m⁻¹) (wL : G) ∈ Subgroup.normalizer (Z : Set G) :=
      hmZ (Subgroup.mem_map.mpr ⟨(wL : G), hwL, rfl⟩)
    have hzmem : (MulAut.conj m⁻¹) (wL : G) * (zL : G) *
        ((MulAut.conj m⁻¹) (wL : G))⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hnorm) (zL : G) |>.mp hzL
    show ((Subgroup.normalizerMonoidHom L ⟨m⁻¹, hmN'⟩ wL * zL *
      (Subgroup.normalizerMonoidHom L ⟨m⁻¹, hmN'⟩ wL)⁻¹ : ↥L) : G) ∈ Z
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, UC6S846.rhoL_mk_coe]
    simpa [MulAut.conj_apply] using hzmem
  have hfix : Zb.map φ.toMonoidHom = Zb :=
    map_eq_of_le_normalizer_of_sylowCenterWeaklyClosed hY Pb hZbPb hZbc hZbcard hQZb φ hφ
  intro y hy
  obtain ⟨z, hzZ, hzy⟩ := Subgroup.mem_map.mp hy
  have hzL : z ∈ L := hQL (hZQ hzZ)
  let zL : ↥L := ⟨z, hzL⟩
  let yL : ↥L := Subgroup.normalizerMonoidHom L ⟨m⁻¹, hmN'⟩ zL
  have hyL : (yL : G) = y := by
    rw [UC6S846.rhoL_mk_coe]
    simpa [MulAut.conj_apply] using hzy
  have hzLmem : zL ∈ Z.subgroupOf L := hzZ
  have hmkz : mkL zL ∈ Zb := Subgroup.mem_map.mpr ⟨zL, hzLmem, rfl⟩
  have hmemphi : mkL yL ∈ Zb := by
    have hphi : mkL yL = φ (mkL zL) := (UC6S846.rhoL_mk L ⟨m⁻¹, hmN'⟩ zL).symm
    rw [hphi]
    exact hfix ▸ Subgroup.mem_map.mpr ⟨mkL zL, hmkz, rfl⟩
  obtain ⟨z', hz'L, hz'eq⟩ := Subgroup.mem_map.mp hmemphi
  have hdiv : yL / z' ∈ CFSG.pCore 2 ↥L :=
    QuotientGroup.eq_iff_div_mem.mp hz'eq.symm
  have hyLsup : yL ∈ (CFSG.pCore 2 ↥L) ⊔ (Z.subgroupOf L) := by
    have h := Subgroup.mul_mem_sup hdiv hz'L
    rwa [div_mul_cancel] at h
  have hyLmemG : (yL : G) ∈ CFSG.Open.pCoreOf 2 L ⊔ Z := by
    rw [CFSG.Open.pCoreOf]
    have hmapmem : (yL : G) ∈ ((CFSG.pCore 2 ↥L) ⊔ (Z.subgroupOf L)).map L.subtype :=
      Subgroup.mem_map.mpr ⟨yL, hyLsup, rfl⟩
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZL] at hmapmem
  rw [← hyL]
  simpa [sup_comm] using hyLmemG

theorem conjugate_eq_of_sylowCenterWeaklyClosed_bar {G : Type} [Group G] [Finite G]
    {D : Data G} {L Q Z : Subgroup G}
    (hY : SylowCenterWeaklyClosed (Bar2 L))
    (hLMle : L ≤ D.M) (hLM : (L.subgroupOf D.M).Normal)
    (hZQ : Z ≤ Q) (hZcentQ : Z ≤ Subgroup.centralizer (Q : Set G)) (hZcard : Nat.card Z = 3)
    (hQL : Q ≤ L) (hQsyl : ∃ S : Sylow 3 ↥L, (S : Subgroup ↥L) = Q.subgroupOf L)
    (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hQZ : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    {m : G} (hm : m ∈ D.M) (hmZ : CFSG.conjugate Z m ≤ Subgroup.normalizer (Z : Set G)) :
    CFSG.conjugate Z m = Z := by
  have hYcard : Nat.card (CFSG.conjugate Z m) = 3 := by
    rw [CFSG.conjugate]
    exact (Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective).trans hZcard
  have hOcard : Nat.Coprime 3 (Nat.card (CFSG.Open.pCoreOf 2 L)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(CFSG.Open.pCoreOf 2 L))).mp
      (UC6S846.isPGroup_pCoreOf L)
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hZO : Z ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz o ho
    rw [CFSG.Open.pCoreOf] at ho ⊢
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp ho
    refine Subgroup.mem_map.mpr ⟨⟨z, hQL (hZQ hz)⟩ * o' * ⟨z, hQL (hZQ hz)⟩⁻¹, ?_, rfl⟩
    exact (CFSG.pCore_normal (p := 2) (G := ↥L)).conj_mem o' ho' ⟨z, hQL (hZQ hz)⟩
  exact eq_of_le_sup_of_le_normalizer hZcard hYcard hOcard hZO
    (conjugate_le_sup_pCoreOf_of_sylowCenterWeaklyClosed hY hLMle hLM hZQ hZcentQ hZcard hQL
      hQsyl hQO2 hQZ hm hmZ)
    hmZ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
