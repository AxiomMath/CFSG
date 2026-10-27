module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivStabShear

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMDivStab_fix_card_le {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x)
    (hindex : ((Bs ⊓ L).subgroupOf Bs).index = 3) {r : MulAut ↥Bs} (ψ : VT → VT)
    (hr : ∀ v : VT, ((r ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
      ((F.thetaT (ψ v) : ↥(Bs ⊓ L)) : G)) :
    Nat.card {b : ↥Bs // r b = b} ≤ 3 * Nat.card {v : VT // ψ v = v} := by
  classical
  haveI : Finite VT := Finite.of_injective F.thetaT F.thetaT.injective
  let H : Subgroup ↥Bs :=
    { carrier := {b | r b = b}
      one_mem' := map_one r
      mul_mem' := by
        intro a b ha hb
        change r (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change r a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let T : Subgroup ↥Bs := (Bs ⊓ L).subgroupOf Bs
  have hrel_le : T.relIndex H ≤ 3 := by
    have h := Subgroup.relIndex_le_of_le_right (H := T) (K := H) (L := ⊤) le_top (by
      rw [Subgroup.relIndex_top_right, hindex]
      norm_num)
    rwa [Subgroup.relIndex_top_right, hindex] at h
  have hcardH : Nat.card ↥H ≤ 3 * Nat.card ↥(H ⊓ T) := by
    have h := Subgroup.relIndex_mul_card T H
    rw [inf_comm] at h
    calc Nat.card ↥H = T.relIndex H * Nat.card ↥(H ⊓ T) := h.symm
      _ ≤ 3 * Nat.card ↥(H ⊓ T) := Nat.mul_le_mul_right _ hrel_le
  have hinj : Nat.card ↥(H ⊓ T) ≤ Nat.card {v : VT // ψ v = v} := by
    let g : ↥(H ⊓ T) → ↥(Bs ⊓ L) := fun b =>
      ⟨((b.1 : ↥Bs) : G),
        Subgroup.mem_inf.mpr ⟨b.1.2,
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp b.2.2)).2⟩⟩
    have hgval : ∀ b : ↥(H ⊓ T), ((g b : ↥(Bs ⊓ L)) : G) = (b.1 : G) := fun b => rfl
    let f : ↥(H ⊓ T) → {v : VT // ψ v = v} := fun b =>
      ⟨F.thetaT.symm (g b), by
        have hv : F.thetaT (F.thetaT.symm (g b)) = g b := F.thetaT.apply_symm_apply _
        have hH : r b.1 = b.1 := b.2.1
        have h := hr (F.thetaT.symm (g b))
        rw [hv] at h
        rw [show (⟨((g b : ↥(Bs ⊓ L)) : G), (g b).2.1⟩ : ↥Bs) = b.1 from
          Subtype.ext (hgval b)] at h
        rw [hH] at h
        have hgoal : F.thetaT (ψ (F.thetaT.symm (g b))) =
            F.thetaT (F.thetaT.symm (g b)) := by
          apply Subtype.ext
          rw [h.symm, F.thetaT.apply_symm_apply]
        exact F.thetaT.injective hgoal⟩
    have hf : Function.Injective f := by
      intro b1 b2 h12
      have h1 : F.thetaT (f b1).1 = F.thetaT (f b2).1 :=
        congrArg (fun z => F.thetaT z.1) h12
      have h2 : g b1 = g b2 := by
        rw [← F.thetaT.apply_symm_apply (g b1), ← F.thetaT.apply_symm_apply (g b2)]
        exact h1
      apply Subtype.ext
      apply Subtype.ext
      calc (b1.1 : G) = ((g b1 : ↥(Bs ⊓ L)) : G) := (hgval b1).symm
        _ = ((g b2 : ↥(Bs ⊓ L)) : G) := congrArg (fun z : ↥(Bs ⊓ L) => (z : G)) h2
        _ = (b2.1 : G) := hgval b2
    exact Nat.card_le_card_of_injective f hf
  calc Nat.card {b : ↥Bs // r b = b} = Nat.card ↥H := rfl
    _ ≤ 3 * Nat.card ↥(H ⊓ T) := hcardH
    _ ≤ 3 * Nat.card {v : VT // ψ v = v} := Nat.mul_le_mul_left 3 hinj

theorem qTwoLMDivStab_stab_card {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x) (hG : GGThmIHyp 3 B x L)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 6 ≤ m)
    (hV : IsQmModel m (QTwoQm m) F.permV) (hVT : IsAugModel m ↥(sumZero m 3) F.permVT)
    (hrigid : ∀ U : Subgroup (QTwoQm m), (∀ (σ : Equiv.Perm (Fin m)) (u : QTwoQm m), u ∈ U →
      F.permV σ u ∈ U) → Nat.card (QTwoQm m) ≤ 3 * Nat.card U →
      ∀ ψ : MulAut (QTwoQm m),
      (∀ σ, ∃ σ', ψ * F.permV σ * ψ⁻¹ = F.permV σ') → (∀ u ∈ U, ψ u = u) → ψ = 1) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩} ≤
      2 * m.factorial := by
  classical
  let Stab : Type := {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩}
  change Nat.card Stab ≤ 2 * m.factorial
  have hform' : ∀ a : Stab, ∃ (π : Equiv.Perm (Fin m)) (ε : Bool), ∀ v : ↥(sumZero m 3),
      ((a.1 ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
        ((F.thetaT (if ε then (F.permVT π v)⁻¹ else F.permVT π v) : ↥(Bs ⊓ L)) : G) :=
    fun a => qTwoLMDivStab_stab_form F hG hL hVT a.1 a.2.1 a.2.2
  choose π ε hπε using hform'
  have hinj : Function.Injective (fun a : Stab => (π a, ε a)) := by
    rintro ⟨a, ha1, ha2⟩ ⟨a', ha1', ha2'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hπ, hε⟩ := h
    have hδT : ∀ b : ↥Bs, (b : G) ∈ L → (a'⁻¹ * a) b = b := by
      intro b hb
      obtain ⟨v, hv⟩ := F.thetaT.surjective ⟨(b : G), ⟨b.2, hb⟩⟩
      have hbw : b = ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val hv).symm
      have h1 := hπε ⟨a, ha1, ha2⟩ v
      have h2 := hπε ⟨a', ha1', ha2'⟩ v
      have h3 : ((a ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
          ((a' ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) := by
        rw [h1, h2, hπ, hε]
      have hb_eq : a b = a' b := by
        rw [hbw]
        exact Subtype.ext h3
      calc (a'⁻¹ * a) b = a'⁻¹ (a b) := rfl
        _ = a'⁻¹ (a' b) := by rw [hb_eq]
        _ = b := by simp
    have hδ : a'⁻¹ * a ∈ ggInduced ⊤ Bs :=
      qTwoLMDivStab_ggInduced_mul (qTwoLMDivStab_ggInduced_inv ha1') ha1
    have hδx : (a'⁻¹ * a) ⟨x, F.hx⟩ = ⟨x, F.hx⟩ := by
      rw [show (a'⁻¹ * a) ⟨x, F.hx⟩ = a'⁻¹ (a ⟨x, F.hx⟩) from rfl, ha2]
      conv_lhs => rw [← ha2']
      simp
    have hδ1 := qTwoLMDivStab_shear F hG hrt hm hV hVT hrigid hδ hδx hδT
    refine Subtype.ext ?_
    have h := congrArg (fun z : MulAut ↥Bs => a' * z) hδ1
    simpa [mul_assoc] using h
  calc Nat.card Stab ≤ Nat.card (Equiv.Perm (Fin m) × Bool) :=
        Nat.card_le_card_of_injective (fun a : Stab => (π a, ε a)) hinj
    _ = m.factorial * 2 := by
        rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
          Nat.card_eq_fintype_card, Fintype.card_bool]
    _ = 2 * m.factorial := mul_comm _ _

theorem qTwoLMDivStab_direct {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x) (hG : GGThmIHyp 3 B x L)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 6 ≤ m)
    (hV : IsQmModel m (QTwoQm m) F.permV) (hVT : IsAugModel m ↥(sumZero m 3) F.permVT)
    (hrigid : ∀ U : Subgroup (QTwoQm m), (∀ (σ : Equiv.Perm (Fin m)) (u : QTwoQm m), u ∈ U →
      F.permV σ u ∈ U) → Nat.card (QTwoQm m) ≤ 3 * Nat.card U →
      ∀ ψ : MulAut (QTwoQm m),
      (∀ σ, ∃ σ', ψ * F.permV σ * ψ⁻¹ = F.permV σ') → (∀ u ∈ U, ψ u = u) → ψ = 1) :
    DirectP3At 3 Bs L x F.hx := by
  intro r hr hrefl hrx
  obtain ⟨π, ε, hπ⟩ := qTwoLMDivStab_stab_form F hG hL hVT r hr hrx
  cases ε
  ·
    obtain ⟨n, hnBs, hn⟩ := F.indT π
    let s : MulAut ↥Bs := ggConjAut Bs hnBs
    have hs_ind : s ∈ ggInduced L Bs := ggConjAut_mem_ggInduced n.2 hnBs
    have hsx : s ⟨x, F.hx⟩ = ⟨x, F.hx⟩ := by
      apply Subtype.ext
      rw [show s = ggConjAut Bs hnBs from rfl, ggConjAut_apply]
      have hxcomm : x * (n : G) = (n : G) * x :=
        Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG n.2) x
          (Set.mem_singleton x)
      rw [show (n : G) * x * (n : G)⁻¹ = x by
        rw [← hxcomm]; group]
    have hrT : ∀ v : ↥(sumZero m 3),
        ((r ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
        ((F.thetaT (F.permVT π v) : ↥(Bs ⊓ L)) : G) := by
      simpa using hπ
    have hsT : ∀ v : ↥(sumZero m 3),
        ((s ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
        ((F.thetaT (F.permVT π v) : ↥(Bs ⊓ L)) : G) := by
      intro v
      rw [show s = ggConjAut Bs hnBs from rfl, ggConjAut_apply]
      exact hn v
    have hδT : ∀ b : ↥Bs, (b : G) ∈ L → (s⁻¹ * r) b = b := by
      intro b hb
      obtain ⟨v, hv⟩ := F.thetaT.surjective ⟨(b : G), ⟨b.2, hb⟩⟩
      have hbw : b = ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val hv).symm
      have hbr : r b = s b := by
        rw [hbw]
        exact Subtype.ext ((hrT v).trans (hsT v).symm)
      calc (s⁻¹ * r) b = s⁻¹ (r b) := rfl
        _ = s⁻¹ (s b) := by rw [hbr]
        _ = b := by simp
    have hs_top : s ∈ ggInduced ⊤ Bs := by
      obtain ⟨g, hgL, hgN, hgs⟩ := hs_ind
      exact ⟨g, Subgroup.mem_top g, hgN, hgs⟩
    have hδ : s⁻¹ * r ∈ ggInduced ⊤ Bs :=
      qTwoLMDivStab_ggInduced_mul (qTwoLMDivStab_ggInduced_inv hs_top) hr
    have hδx : (s⁻¹ * r) ⟨x, F.hx⟩ = ⟨x, F.hx⟩ := by
      rw [show (s⁻¹ * r) ⟨x, F.hx⟩ = s⁻¹ (r ⟨x, F.hx⟩) from rfl, hrx]
      conv_lhs => rw [← hsx]
      simp
    have h1 := qTwoLMDivStab_shear F hG hrt hm hV hVT hrigid hδ hδx hδT
    have hrs : r = s := by
      have h := congrArg (fun z : MulAut ↥Bs => s * z) h1
      simpa [mul_assoc] using h
    rw [hrs]
    exact Subgroup.subset_closure hs_ind
  ·
    have hπ' : ∀ v : ↥(sumZero m 3),
        ((r ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
          ((F.thetaT ((F.permVT π v)⁻¹) : ↥(Bs ⊓ L)) : G) := by
      intro v
      simpa using hπ v
    unfold GGIsReflection at hrefl
    obtain ⟨hr2, hrfix⟩ := hrefl
    let b : ↥(sumZero m 3) → ↥Bs := fun v =>
      ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩
    have hb_eq : ∀ v : ↥(sumZero m 3), r (b v) = b ((F.permVT π v)⁻¹) := by
      intro v
      apply Subtype.ext
      simpa [b] using hπ' v
    have hfixr : ∀ x : ↥Bs, r (r x) = x := by
      intro x
      have hx := congrArg (fun f : MulAut ↥Bs => f x) hr2
      simpa [pow_two, MulAut.mul_apply] using hx
    have hπ2 : π * π = 1 := by
      apply qTwoLMFrameC_perm_faithful hVT
      intro v
      have h1 : r (b v) = b ((F.permVT π v)⁻¹) := hb_eq v
      have h2 : r (b ((F.permVT π v)⁻¹)) = b v := by
        rw [← h1]
        exact hfixr (b v)
      have h3 : F.thetaT ((F.permVT π ((F.permVT π v)⁻¹))⁻¹) = F.thetaT v := by
        apply Subtype.ext
        rw [← hπ' ((F.permVT π v)⁻¹)]
        exact congrArg (fun z : ↥Bs => (z : G)) h2
      have h4 : (F.permVT π ((F.permVT π v)⁻¹))⁻¹ = v := F.thetaT.injective h3
      have h5 : F.permVT (π * π) v = (F.permVT π ((F.permVT π v)⁻¹))⁻¹ := by
        rw [map_inv, inv_inv, ← MulAut.mul_apply, ← map_mul]
      exact h5.trans h4
    have hψcard : Nat.card {v : ↥(sumZero m 3) // (F.permVT π v)⁻¹ = v} ≤ 3 ^ (m / 2) := by
      have heq : Nat.card {v : ↥(sumZero m 3) // (F.permVT π v)⁻¹ = v}
          = Nat.card {v : ↥(sumZero m 3) // F.permVT π v = v⁻¹} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun v => inv_eq_iff_eq_inv))
      rw [heq]
      exact qTwoLMFrameC_negFix_card_le_VT hVT hπ2
    have hcardBs : Nat.card ↥Bs = 3 ^ m := qTwoLMDivStab_card_Bs F (by omega) hV
    have hcardT0 : Nat.card ↥(Bs ⊓ L) = 3 ^ (m - 1) := qTwoLMFrameC_card_T F hVT
    have hcardT : Nat.card ↥((Bs ⊓ L).subgroupOf Bs) = 3 ^ (m - 1) := by
      rw [← hcardT0]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hindex : ((Bs ⊓ L).subgroupOf Bs).index = 3 := by
      have h := Subgroup.card_mul_index ((Bs ⊓ L).subgroupOf Bs)
      rw [hcardT, hcardBs] at h
      have hpow : 3 ^ m = 3 ^ (m - 1) * 3 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hpow] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    have hfix := qTwoLMDivStab_fix_card_le F hindex (fun v => (F.permVT π v)⁻¹) hπ'
    have hle : 3 ^ m ≤ 3 ^ (m / 2 + 2) := by
      calc 3 ^ m = Nat.card ↥Bs := hcardBs.symm
        _ = Nat.card {b : ↥Bs // r b = b} * 3 := hrfix.symm
        _ ≤ (3 * Nat.card {v : ↥(sumZero m 3) // (F.permVT π v)⁻¹ = v}) * 3 :=
            mul_le_mul_left hfix 3
        _ ≤ (3 * 3 ^ (m / 2)) * 3 := mul_le_mul_left (mul_le_mul_right hψcard 3) 3
        _ = 3 ^ (m / 2 + 2) := by rw [pow_add]; ring
    have hle2 : m ≤ m / 2 + 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    omega

theorem qTwoLMDivStab_stabDirect_of_rigid {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G}
    {x : G} {D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x) (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hFrameL : QTwoFrameL 3 B Bs x L D J)
    (hFm : hFrameL.m = m) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hV : IsQmModel m (QTwoQm m) F.permV) (hVT : IsAugModel m ↥(sumZero m 3) F.permVT)
    (hrigid : ∀ U : Subgroup (QTwoQm m), (∀ (σ : Equiv.Perm (Fin m)) (u : QTwoQm m), u ∈ U →
      F.permV σ u ∈ U) → Nat.card (QTwoQm m) ≤ 3 * Nat.card U →
      ∀ ψ : MulAut (QTwoQm m),
      (∀ σ, ∃ σ', ψ * F.permV σ * ψ⁻¹ = F.permV σ') → (∀ u ∈ U, ψ u = u) → ψ = 1) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩} ≤
        2 * m.factorial ∧
      DirectP3At 3 Bs L x F.hx :=
  ⟨qTwoLMDivStab_stab_card F hG hL hrt hm hV hVT hrigid,
    qTwoLMDivStab_direct F hG hL hrt hm hV hVT hrigid⟩

end CFSG.StandardType.QTwo

end
