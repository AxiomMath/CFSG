module

public import CFSG.Quasithin.Vol2.Ch12Sec8Three
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111
public import CFSG.Quasithin.EmptyFaithful.S1421L246

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem eq_one_of_mem_oddCoreIn_of_mul_self {H : Subgroup G} {u : G} (hu : u ∈ oddCoreIn H)
    (h2 : u * u = 1) : u = 1 := by
  have hodd := odd_card_oddCoreIn H
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreIn H)) :=
    (Nat.coprime_two_left).mpr hodd
  set x : ↥(oddCoreIn H) := ⟨u, hu⟩ with hx
  have h1 : orderOf x ∣ Nat.card (oddCoreIn H) := orderOf_dvd_natCard x
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [sq] using h2)
  have h2' : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h2' h1
    rwa [hcop] at this
  have : x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  simpa [hx] using congrArg Subtype.val this

theorem oddCoreIn_g0_eq_bot (st : Setting1427 T M H K1) {G0 : Subgroup G}
    (hYG0 : yOfL22 T M ≤ G0) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hinv : ∀ y ∈ oddCoreIn G0, z⁻¹ * y * z = y⁻¹) : oddCoreIn G0 = ⊥ := by
  have h1281 := lemma_14_2_4 st.hyp st.facts
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hz
  obtain ⟨v, hvV, hvZ⟩ : ∃ v ∈ VZ T M, v ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    have hle : VZ T M ≤ quasithinOmegaOneCenter T := fun v hv => hall v hv
    have := Subgroup.card_le_of_le hle
    rw [st.hyp.rank_two, st.hyp.card_omegaOneCenter] at this
    omega
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Subgroup.one_mem _)
  have hzvV : z * v ∈ VZ T M := (VZ T M).mul_mem hzV hvV
  have hzv1 : z * v ≠ 1 := by
    intro h
    apply hvZ
    have : v = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ hz
  have key : ∀ w ∈ VZ T M, w ≠ 1 → ∀ u ∈ oddCoreIn G0, w⁻¹ * u * w = u⁻¹ := by
    intro w hw hw1 u hu
    obtain ⟨y, hy, hyw⟩ := h1281.exists_conj_eq hzV hw hz1 hw1
    have hyG0 : y ∈ G0 := hYG0 hy
    have hu' : y⁻¹ * u * y ∈ oddCoreIn G0 := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn G0 (G0.inv_mem hyG0)) u).mp
        hu
      simpa using this
    have h2 := hinv _ hu'
    rw [← hyw]
    calc (y * z * y⁻¹)⁻¹ * u * (y * z * y⁻¹) = y * (z⁻¹ * (y⁻¹ * u * y) * z) * y⁻¹ := by group
      _ = y * (y⁻¹ * u * y)⁻¹ * y⁻¹ := by rw [h2]
      _ = u⁻¹ := by group
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hz' := hinv u hu
  have hv' := key v hvV hv1 u hu
  have hzv' := key (z * v) hzvV hzv1 u hu
  have e1 : (z * v)⁻¹ * u * (z * v) = u := by
    calc (z * v)⁻¹ * u * (z * v) = v⁻¹ * (z⁻¹ * u * z) * v := by group
      _ = v⁻¹ * u⁻¹ * v := by rw [hz']
      _ = (v⁻¹ * u * v)⁻¹ := by group
      _ = (u⁻¹)⁻¹ := by rw [hv']
      _ = u := inv_inv u
  rw [hzv'] at e1
  exact eq_one_of_mem_oddCoreIn_of_mul_self hu (mul_eq_one_iff_eq_inv.mpr e1.symm)

theorem isSolvable_yOfL22_sup (st : Setting1427 T M H K1) :
    Group.IsSolvable ↥(yOfL22 T M ⊔ T) := by
  obtain ⟨e⟩ := st.facts.sThree
  have h3 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have hq : Group.IsSolvable (OTwoQuot (yOfL22 T M ⊔ T)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact B6.isSolvable_of_quotient_pCore hq

omit [Finite G] in
theorem isSolvable_quotient_of_sup {G0 L W X : Subgroup G}
    (hLn : (L.subgroupOf G0).Normal) (hG0 : G0 = L ⊔ W) (hWX : W ≤ X)
    (hX : Group.IsSolvable ↥X) : Group.IsSolvable (↥G0 ⧸ L.subgroupOf G0) := by
  have hLG0 : L ≤ G0 := hG0 ▸ le_sup_left
  have hWG0 : W ≤ G0 := hG0 ▸ le_sup_right
  have : Group.IsSolvable ↥W := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hWX)
  let f : ↥W →* ↥G0 ⧸ L.subgroupOf G0 :=
    (QuotientGroup.mk' (L.subgroupOf G0)).comp (Subgroup.inclusion hWG0)
  refine Group.isSolvable_of_surjective (f := f) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hsup : L.subgroupOf G0 ⊔ W.subgroupOf G0 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLG0 hWG0, ← hG0, Subgroup.subgroupOf_self]
  have hxmem : x ∈ L.subgroupOf G0 ⊔ W.subgroupOf G0 := by
    rw [hsup]
    exact Subgroup.mem_top x
  obtain ⟨n, hn, w, hw, hnw⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := L.subgroupOf G0) (t := W.subgroupOf G0)).mp hxmem
  refine ⟨⟨(w : G), hw⟩, ?_⟩
  have hinc : Subgroup.inclusion hWG0 ⟨(w : G), hw⟩ = w := Subtype.ext rfl
  show QuotientGroup.mk' (L.subgroupOf G0) (Subgroup.inclusion hWG0 ⟨(w : G), hw⟩) =
    QuotientGroup.mk x
  rw [hinc, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hnw]
  have := hLn.conj_mem n hn w⁻¹
  simpa [mul_assoc] using this

theorem isSolvable_quotient_g0 (st : Setting1427 T M H K1) {G0 L : Subgroup G}
    (hLn : (L.subgroupOf G0).Normal) (hG0 : G0 = L ⊔ yOfL22 T M ⊔ sOf T K1) :
    Group.IsSolvable (↥G0 ⧸ L.subgroupOf G0) := by
  refine isSolvable_quotient_of_sup hLn (W := yOfL22 T M ⊔ sOf T K1) ?_ ?_
    (isSolvable_yOfL22_sup st)
  · rw [hG0, sup_assoc]
  · exact sup_le_sup_left sOf_le_T _

end S1421

end CFSG.Quasithin
