module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsComp
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_mem_irrSet_of_ne_bot {H : Subgroup (MulAut W)} (hH : QuadTrivial H)
    (hne : H ≠ ⊥) : ∃ I : Subgroup W, I ∈ irrSet H := by
  have hM : StableUnder H (⊤ : Subgroup W) := fun _ _ _ _ => Subgroup.mem_top _
  have hne' : commSub (⊤ : Subgroup W) H ≠ ⊥ := by
    intro h
    have h1 : (⊤ : Subgroup W) ≤ fixV H := commSub_eq_bot_iff.mp h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact MulEquiv.ext fun w => (mem_fixV.mp (h1 (Subgroup.mem_top w))) x hx
  obtain ⟨I, hI, -⟩ := exists_mem_irrSet_le hH hM hne'
  exact ⟨I, hI⟩

private theorem gf2_Kernel_conj_mem_inf_centSub {Y A : Subgroup (MulAut W)}
    (hA : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A) {U : Subgroup W} (hU : StableUnder Y U) :
    ∀ y ∈ Y, ∀ m ∈ A ⊓ centSub U, y * m * y⁻¹ ∈ A ⊓ centSub U := by
  intro y hy m hm
  refine Subgroup.mem_inf.mpr ⟨hA y hy m hm.1, ?_⟩
  rw [mem_centSub]
  intro u hu
  have h1 : y⁻¹ u ∈ U := hU y⁻¹ (Y.inv_mem hy) u hu
  have h2 : m (y⁻¹ u) = y⁻¹ u := (mem_centSub.mp hm.2) _ h1
  calc (y * m * y⁻¹) u = y (m (y⁻¹ u)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = y (y⁻¹ u) := by rw [h2]
    _ = u := MulEquiv.apply_symm_apply y u

theorem faithful_on_iSup_irrSet (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hL : CFSG.Open.IsComponentOf L Y)
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) (hne : H ≠ ⊥) (hHY : H ≤ Y)
    (hHn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) :
    ∀ h ∈ H, (∀ u ∈ (⨆ I ∈ irrSet H, I), h u = u) → h = 1 := by
  have hQ : QuadTrivial H := by
    rw [hH]
    exact quadTrivial_biSup_conj hL.2.2.1 Y
  have hU : StableUnder Y (⨆ I ∈ irrSet H, I) := stableUnder_iSup_irrSet hHn
  obtain ⟨I₀, hI₀⟩ := exists_mem_irrSet_of_ne_bot hQ hne
  have hIU : ∀ I ∈ irrSet H, I ≤ ⨆ I ∈ irrSet H, I := fun I hI => le_iSup₂_of_le I hI le_rfl
  have hI₀U : I₀ ≤ ⨆ I ∈ irrSet H, I := hIU I₀ hI₀
  have hMY : H ⊓ centSub (⨆ I ∈ irrSet H, I) ≤ Y := inf_le_left.trans hHY
  have hMn := gf2_Kernel_conj_mem_inf_centSub hHn hU
  have hLM : ¬ L ≤ H ⊓ centSub (⨆ I ∈ irrSet H, I) := by
    intro hLM
    have hHM : H ≤ H ⊓ centSub (⨆ I ∈ irrSet H, I) := biSup_conj_le_of_normal hH hMn hLM
    apply not_le_fixV_of_mem_irrSet hI₀
    intro w hw
    rw [mem_fixV]
    intro h hh
    exact (mem_centSub.mp (hHM hh).2) w (hI₀U hw)
  have hcomm := commute_of_normal_of_not_le hL hH hMY hMn hLM
  have hab : ∀ m ∈ H ⊓ centSub (⨆ I ∈ irrSet H, I), ∀ n ∈ H ⊓ centSub (⨆ I ∈ irrSet H, I),
      m * n = n * m := fun m hm n hn => hcomm m hm n hn.1
  have hodd := odd_card_of_abelian_normal hO hMY hMn hab
  have hbot : H ⊓ centSub (⨆ I ∈ irrSet H, I) = ⊥ := by
    refine eq_bot_of_trivial_on_irrSet hW hodd hQ ?_ ?_ ?_
    · intro h hh x hx
      exact hMn h (hHY hh) x hx
    · intro I hI x hx w hw
      exact (mem_centSub.mp hx.2) w (hIU I hI hw)
    · intro x hx w hw
      exact (mem_fixV.mp hw) x hx.1
  intro h hh hfix
  have hmem : h ∈ H ⊓ centSub (⨆ I ∈ irrSet H, I) := ⟨hh, mem_centSub.mpr hfix⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem le_iSup_irrSet_sup_fixV {Y L H : Subgroup (MulAut W)}
    (hL : CFSG.Open.IsComponentOf L Y) (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) :
    (⨆ I ∈ irrSet H, I) ≤ (⨆ J ∈ irrSet L, J) ⊔ fixV L := by
  have hLH : L ≤ H := le_of_eq_biSup_conj hH
  have hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := conj_mem_of_eq_biSup_conj hL hH
  have hQL : QuadTrivial L := quadTrivial_of_commutator_eq_top hL.2.2.1
  have hfix : fixV H ≤ fixV L := fun w hw x hx => hw x (hLH hx)
  refine iSup₂_le fun I hI => ?_
  by_cases hcomm : commSub I L = ⊥
  · exact le_sup_of_le_right (commSub_eq_bot_iff.mp hcomm)
  · have hIL : StableUnder L I := fun x hx u hu => (stableUnder_of_mem_irrSet hI) x (hLH hx) u hu
    obtain ⟨J, hJ, hJI⟩ := exists_mem_irrSet_le hQL hIL hcomm
    let S : Set (Subgroup W) := {K | ∃ h ∈ H, K = J.map h.toMonoidHom}
    have hSclosed : ∀ K ∈ S, ∀ y ∈ H, K.map y.toMonoidHom ∈ S := by
      rintro K ⟨h, hh, rfl⟩ y hy
      refine ⟨y * h, H.mul_mem hy hh, ?_⟩
      rw [Subgroup.map_map]
      rfl
    have hTstable : StableUnder H (⨆ K ∈ S, K) := stableUnder_iSup_of_map_mem hSclosed
    have hJS : J ∈ S := ⟨1, H.one_mem, by ext w; simp⟩
    have hSL : ∀ K ∈ S, K ∈ irrSet L := by
      rintro K ⟨h, hh, rfl⟩
      refine map_mem_irrSet (hLn h hh) ?_ hJ
      intro x hx
      simpa using hLn h⁻¹ (H.inv_mem hh) x hx
    have hTle : (⨆ K ∈ S, K) ≤ ⨆ J' ∈ irrSet L, J' :=
      iSup₂_le fun K hK => le_iSup₂_of_le K (hSL K hK) le_rfl
    have hTI : (⨆ K ∈ S, K) ≤ I := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨h, hh, rfl⟩ := hK
      rintro _ ⟨u, hu, rfl⟩
      exact (stableUnder_of_mem_irrSet hI) h hh u (hJI hu)
    have hJT : J ≤ ⨆ K ∈ S, K := le_iSup₂_of_le J hJS le_rfl
    have hPstab : StableUnder H ((⨆ K ∈ S, K) ⊔ (I ⊓ fixV H)) :=
      stableUnder_sup hTstable hI.2.2.2.1
    have hPle : (⨆ K ∈ S, K) ⊔ (I ⊓ fixV H) ≤ I := sup_le hTI inf_le_left
    rcases hI.2.2.2.2 _ hPstab le_sup_right hPle with hP | hP
    · exfalso
      apply not_le_fixV_of_mem_irrSet hJ
      have hJC : J ≤ I ⊓ fixV H := by
        rw [← hP]
        exact hJT.trans le_sup_left
      exact (hJC.trans inf_le_right).trans hfix
    · calc I = (⨆ K ∈ S, K) ⊔ (I ⊓ fixV H) := hP.symm
        _ ≤ (⨆ J' ∈ irrSet L, J') ⊔ fixV L := sup_le_sup hTle (inf_le_right.trans hfix)

theorem faithful_on_sup_fixV (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hL : CFSG.Open.IsComponentOf L Y)
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) (hne : H ≠ ⊥) (hHY : H ≤ Y)
    (hHn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) :
    ∀ y ∈ Y, (∀ u ∈ (⨆ I ∈ irrSet H, I) ⊔ fixV H, y u = u) → y = 1 := by
  have hQ : QuadTrivial H := by
    rw [hH]
    exact quadTrivial_biSup_conj hL.2.2.1 Y
  have hW'stable : StableUnder Y ((⨆ I ∈ irrSet H, I) ⊔ fixV H) :=
    stableUnder_sup (stableUnder_iSup_irrSet hHn) (stableUnder_fixV hHn)
  have hIU : ∀ I ∈ irrSet H, I ≤ ⨆ I ∈ irrSet H, I := fun I hI => le_iSup₂_of_le I hI le_rfl
  have hUW' : (⨆ I ∈ irrSet H, I) ≤ (⨆ I ∈ irrSet H, I) ⊔ fixV H := le_sup_left
  have hCW' : fixV H ≤ (⨆ I ∈ irrSet H, I) ⊔ fixV H := le_sup_right
  have hNn := gf2_Kernel_conj_mem_inf_centSub
    (fun y hy a ha => Y.mul_mem (Y.mul_mem hy ha) (Y.inv_mem hy)) hW'stable
  have hNY : Y ⊓ centSub ((⨆ I ∈ irrSet H, I) ⊔ fixV H) ≤ Y := inf_le_left
  have hNbot : Y ⊓ centSub ((⨆ I ∈ irrSet H, I) ⊔ fixV H) = ⊥ := by
    by_contra hne'
    obtain ⟨x, hxN, hx1, hxodd⟩ := exists_odd_orderOf_of_normal_ne_bot hO hNY hNn hne'
    have hXodd : Odd (Nat.card (Subgroup.zpowers x)) := by
      rw [Nat.card_zpowers]
      exact hxodd
    have hXN : Subgroup.zpowers x ≤ Y ⊓ centSub ((⨆ I ∈ irrSet H, I) ⊔ fixV H) :=
      (Subgroup.zpowers_le).2 hxN
    have hcomm : ∀ n ∈ Y ⊓ centSub ((⨆ I ∈ irrSet H, I) ⊔ fixV H), ∀ h ∈ H,
        h * n * h⁻¹ = n := by
      intro n hn h hh
      have hc1 : h * n * h⁻¹ * n⁻¹ ∈ Y ⊓ centSub ((⨆ I ∈ irrSet H, I) ⊔ fixV H) :=
        Subgroup.mul_mem _ (hNn h (hHY hh) n hn) (Subgroup.inv_mem _ hn)
      have hc2 : h * n * h⁻¹ * n⁻¹ ∈ H := by
        have h3 := hHn n hn.1 h⁻¹ (H.inv_mem hh)
        have e : h * n * h⁻¹ * n⁻¹ = h * (n * h⁻¹ * n⁻¹) := by group
        rw [e]
        exact H.mul_mem hh h3
      have h4 := faithful_on_iSup_irrSet hW hO hL hH hne hHY hHn _ hc2
        (fun u hu => (mem_centSub.mp hc1.2) u (hUW' hu))
      exact mul_inv_eq_one.mp h4
    have hX : Subgroup.zpowers x = ⊥ := by
      refine eq_bot_of_trivial_on_irrSet hW hXodd hQ ?_ ?_ ?_
      · intro h hh z hz
        rw [hcomm z (hXN hz) h hh]
        exact hz
      · intro I hI z hz w hw
        exact (mem_centSub.mp (hXN hz).2) w (hUW' (hIU I hI hw))
      · intro z hz w hw
        exact (mem_centSub.mp (hXN hz).2) w (hCW' hw)
    have hxX : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [hX] at hxX
    exact hx1 (Subgroup.mem_bot.mp hxX)
  intro y hy hfix
  have hmem : y ∈ Y ⊓ centSub ((⨆ I ∈ irrSet H, I) ⊔ fixV H) := ⟨hy, mem_centSub.mpr hfix⟩
  rw [hNbot] at hmem
  exact Subgroup.mem_bot.mp hmem

end CFSG.LocalAnalysis.WeakClosure81
