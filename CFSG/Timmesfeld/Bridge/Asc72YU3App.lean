module

public import CFSG.Timmesfeld.Bridge.Asc72YU3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem
public import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.Timmesfeld.Bridge.Asc72YWidth

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki
open scoped commutatorElement

theorem map_zStar_le {Y : Type} [Group Y] (ψ : MulAut Y) :
    (zStar Y).map ψ.toMonoidHom ≤ zStar Y := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_zStar_iff] at hx
  rw [mem_zStar_iff]
  intro h
  have hchar : (CFSG.pCore 2 Y).map ψ.toMonoidHom = CFSG.pCore 2 Y :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance ψ
  have h1 : ⁅ψ.toMonoidHom x, h⁆ = ψ.toMonoidHom ⁅x, ψ.symm h⁆ := by
    rw [map_commutatorElement]
    simp
  rw [h1, ← hchar]
  exact Subgroup.mem_map_of_mem _ (hx _)

theorem map_zStar_eq {Y : Type} [Group Y] (ψ : MulAut Y) :
    (zStar Y).map ψ.toMonoidHom = zStar Y := by
  refine le_antisymm (map_zStar_le ψ) fun x hx => ?_
  refine ⟨ψ.symm x, map_zStar_le ψ⁻¹ ⟨x, hx, rfl⟩, ?_⟩
  simp

variable {G : Type} [Group G] {D : Set G}

theorem conj_mem_localGroup (hN : IsNormalSet D) {z a x : G} (haz : Commute a z)
    (hx : x ∈ localGroup D z) : a * x * a⁻¹ ∈ localGroup D z := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine mem_localGroup_of_mem ⟨hN a y hy.1, ?_⟩
    have h := (Commute.conj_iff a).mpr hy.2
    rwa [haz.eq, mul_inv_cancel_right] at h
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx


theorem false_of_psu3 [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hZ : Subgroup.center G = ⊥) (hnsq : ¬ MeetsSq D) {u w v : G} (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
    (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
      (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n)
    (hU : Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
      PSU3Model 2)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hS.oddT
  obtain ⟨hzz, hz1, hzu, hzv, hzw, -⟩ := htri.third_kind hD hS.normal hn hord
  obtain ⟨hu', hv', -, huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have hzH := thirdKind_z_mem_localGroup hS htri hn hord
  have hSH := localSetup hS htri hn hord huw
  have hdiscH := localSet_disconnected hS htri hn hord huw
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  set H := localGroup D ((u * v * w) ^ n) with hHdef
  have hz'c : (⟨(u * v * w) ^ n, hzH⟩ : H) ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
  have : (Subgroup.zpowers (⟨(u * v * w) ^ n, hzH⟩ : H)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hO2' : CFSG.pCore 2 H ≤ Subgroup.zpowers (⟨(u * v * w) ^ n, hzH⟩ : H) := by
    intro q hq
    rcases hO2 q hq with h | h
    · rw [show q = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show q = ⟨(u * v * w) ^ n, hzH⟩ from Subtype.ext h]
      exact Subgroup.mem_zpowers _
  set u' : H := ⟨u, mem_localGroup_of_mem hu'⟩ with hu'def
  set v' : H := ⟨v, mem_localGroup_of_mem hv'⟩ with hv'def
  set d' : H := ⟨u * v * (u * v * w) ^ n, mem_localGroup_of_mem huvz⟩ with hd'def
  have hu'L : u' ∈ localSet D ((u * v * w) ^ n) := hu'
  have hv'L : v' ∈ localSet D ((u * v * w) ^ n) := hv'
  have hd'L : u' * v' * ⟨(u * v * w) ^ n, hzH⟩ ∈ localSet D ((u * v * w) ^ n) := huvz
  have hpair : ({u', v', d'} : Set H).Pairwise Commute := by
    have huv := htri.2.2.2.2.1
    have hdab := (hD.commute_mul_iff htri.1 htri.2.1 huvz.1 htri.2.2.2.1 huv).mp
      ((Commute.refl (u * v)).mul_left (hzu.mul_right hzv))
    have h1 : Commute u' v' := commute_coe_iff.mp huv
    have h2 : Commute u' d' := commute_coe_iff.mp hdab.1.symm
    have h3 : Commute v' d' := commute_coe_iff.mp hdab.2.symm
    have h1' := h1.symm; have h2' := h2.symm; have h3' := h3.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hA : IsPGroup 2 (Subgroup.closure ({u', v', d'} : Set H)) := by
    refine isPGroup_closure_of_pairwise hpair ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact Subtype.ext (hD.mul_self_eq_one htri.1)
    · exact Subtype.ext (hD.mul_self_eq_one htri.2.1)
    · exact Subtype.ext (hD.mul_self_eq_one huvz.1)
  obtain ⟨T₀, hT₀⟩ := hA.exists_le_sylow
  have hmemT : ∀ s ∈ ({u', v', d'} : Set H), s ∈ T₀ := fun s hs =>
    hT₀ (Subgroup.subset_closure hs)
  obtain ⟨S₀, hS₀⟩ := (T₀.isPGroup'.map H.subtype).exists_le_sylow
  have hTS : ∀ x : H, x ∈ T₀ → (x : G) ∈ S₀ := fun x hx => hS₀ ⟨x, hx, rfl⟩
  have huS : u ∈ S₀ := hTS u' (hmemT u' (by simp))
  have hvS : v ∈ S₀ := hTS v' (hmemT v' (by simp))
  have hdS : u * v * (u * v * w) ^ n ∈ S₀ := hTS d' (hmemT d' (by simp))
  obtain ⟨-, hzc, a, haS, hane, -, haa, -, hfix⟩ :=
    sylow_data hS hrad hZ hnsq htri hn hord huw hO2 S₀ huS hvS hdS
  have hST : ∀ x : H, (x : G) ∈ S₀ → x ∈ T₀ := by
    intro x hx
    have hP : IsPGroup 2 ((S₀ : Subgroup G).comap H.subtype) := S₀.isPGroup'.comap_subtype
    have hle : (T₀ : Subgroup H) ≤ (S₀ : Subgroup G).comap H.subtype := fun y hy => hTS y hy
    have h := T₀.is_maximal' hP hle
    show x ∈ (T₀ : Subgroup H)
    rw [← h]
    exact hx
  have haz : Commute a ((u * v * w) ^ n) := hzc a haS
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hmapH : H.map (MulAut.conj a).toMonoidHom = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact conj_mem_localGroup hS.normal haz hx
    · intro x hx
      refine ⟨a * x * a⁻¹, conj_mem_localGroup hS.normal haz hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hainv]
      rw [show a * (a * x * a) * a = (a * a) * x * (a * a) by group, haa, one_mul, mul_one]
  let φ : MulAut H := ((MulAut.conj a).subgroupMap H).trans (MulEquiv.subgroupCongr
    ((show H.map (MulAut.conj a : G →* G) = H.map (MulAut.conj a).toMonoidHom from rfl).trans
      hmapH))
  have hφ : ∀ x : H, ((φ x : H) : G) = a * x * a⁻¹ := fun x => rfl
  have hφφ : ∀ x : H, φ (φ x) = x := fun x => Subtype.ext (by
    rw [hφ, hφ, hainv, show a * (a * (x : G) * a) * a = (a * a) * x * (a * a) by group, haa,
      one_mul, mul_one])
  set π := QuotientGroup.mk' (zStar H) with hπdef
  let α : MulAut (H ⧸ zStar H) := QuotientGroup.congr (zStar H) (zStar H) φ (map_zStar_eq φ)
  have hα : ∀ x : H, α (π x) = π (φ x) := fun x =>
    QuotientGroup.congr_mk (zStar H) (zStar H) φ (map_zStar_eq φ) x
  have hαα : α * α = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zStar H) q
    rw [MulAut.mul_apply, hα, hα, hφφ, MulAut.one_apply]
  set Q : Sylow 2 (H ⧸ zStar H) := T₀.mapSurjective (QuotientGroup.mk'_surjective (zStar H))
  have hQ : (Q : Subgroup (H ⧸ zStar H)) = (T₀ : Subgroup H).map π := Sylow.coe_mapSurjective _ _
  have hφT : ∀ x : H, x ∈ T₀ → φ x ∈ T₀ := fun x hx =>
    hST _ (by rw [hφ]; exact S₀.mul_mem (S₀.mul_mem haS (hTS x hx)) (S₀.inv_mem haS))
  have hαQ : ∀ s ∈ (Q : Subgroup (H ⧸ zStar H)), α s ∈ (Q : Subgroup (H ⧸ zStar H)) := by
    intro s hs
    rw [hQ] at hs ⊢
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hα]
    exact ⟨φ t, hφT t ht, rfl⟩
  obtain ⟨e⟩ := hU
  have hmodel : PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [PSU3Model, CFSG.Open.PSU3]
  let e' : H ⧸ zStar H ≃* CFSG.Open.PSU3 2 2 := e.trans (MulEquiv.subgroupCongr hmodel)
  obtain ⟨-, hB'⟩ := CentralQuot.quot_facts hz'c (Subtype.ext hzz) hSH (fun h => hzD h.1) hdiscH
    hu'L hv'L (fun h => htri.2.2.2.1 (congrArg Subtype.val h))
    (commute_coe_iff.mp htri.2.2.2.2.1) hd'L
  have hB := CentralQuot.isBenderGroup_zStar (Subtype.ext hzz) hB'
  have hfixQ : ∀ x ∈ (Q : Subgroup (H ⧸ zStar H)), x * x = 1 → α x = x := fun x hxQ hxx =>
    YU3.fix_center_of_mulEquiv_psu3 (f := 2) le_rfl e' Q α hαα hαQ hxQ
      (IsBenderGroup.commute_of_mul_self_eq_one hB Q hxQ hxx)
  have hcommL : ∀ ℓ : H, ℓ ∈ localSet D ((u * v * w) ^ n) → ℓ ∈ T₀ → Commute a (ℓ : G) := by
    intro ℓ hℓL hℓT
    have hℓℓ : ℓ * ℓ = 1 := Subtype.ext (hD.mul_self_eq_one hℓL.1)
    have hπQ : π ℓ ∈ (Q : Subgroup (H ⧸ zStar H)) := by
      rw [hQ]
      exact ⟨ℓ, hℓT, rfl⟩
    have h1 := hfixQ _ hπQ (by rw [← map_mul, hℓℓ, map_one])
    rw [hα] at h1
    have h2 : (φ ℓ)⁻¹ * ℓ ∈ zStar H := QuotientGroup.eq.mp h1
    have h3 := CentralQuot.mem_zpowers_of_mem_zStar (Subtype.ext hzz) hO2' T₀.isPGroup'
      (T₀.mul_mem (T₀.inv_mem (hφT ℓ hℓT)) hℓT) h2
    rcases (mem_zpowers_of_mul_self (Subtype.ext hzz :
        (⟨(u * v * w) ^ n, hzH⟩ : H) * ⟨(u * v * w) ^ n, hzH⟩ = 1)).mp h3 with h4 | h4
    · have h5 : φ ℓ = ℓ := inv_mul_eq_one.mp h4
      have h6 : a * (ℓ : G) * a⁻¹ = ℓ := by rw [← hφ, h5]
      show a * ℓ = ℓ * a
      calc a * (ℓ : G) = a * ℓ * a⁻¹ * a := by group
        _ = ℓ * a := by rw [h6]
    · exfalso
      have h5 : (a * (ℓ : G) * a⁻¹)⁻¹ * ℓ = (u * v * w) ^ n := by
        have := congrArg Subtype.val h4
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hφ] using this
      have hℓD : (ℓ : G) ∈ D := hℓL.1
      have haℓD : a * (ℓ : G) * a⁻¹ ∈ D := hS.conj_mem a hℓD
      have hℓS := hTS ℓ hℓT
      have haℓS : a * (ℓ : G) * a⁻¹ ∈ S₀ := S₀.mul_mem (S₀.mul_mem haS hℓS) (S₀.inv_mem haS)
      have hc : Commute (a * (ℓ : G) * a⁻¹) ℓ :=
        hD.commute_of_isPGroup S₀.isPGroup' haℓD hℓD haℓS hℓS
      have hne : a * (ℓ : G) * a⁻¹ ≠ ℓ := by
        intro h
        apply hz1
        rw [← h5, h, inv_mul_cancel]
      exact false_of_eq_mul_of_not_reach hS htri.1 htri.2.2.1 hzu.symm hzw.symm huw haℓD hℓD
        hne hc (by rw [← h5, hD.inv_eq haℓD])
  exact hfix ⟨u, ⟨htri.1, huS⟩, v, ⟨htri.2.1, hvS⟩, htri.2.2.2.1,
    hcommL u' hu'L (hmemT u' (by simp)), hcommL v' hv'L (hmemT v' (by simp))⟩

end CFSG.Timmesfeld.Bridge.Asc72
