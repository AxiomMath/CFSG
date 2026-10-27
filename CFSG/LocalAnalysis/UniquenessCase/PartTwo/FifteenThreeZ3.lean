module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section CaseThree

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

@[expose] def RTenP153 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V →
    ∀ [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal],
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ n : ℕ, 1 < n →
    ∀ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal → IsElemAbelian p Xbar →
      Nat.card Xbar = p ^ n → Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ →
        Nat.card V₀ < 8

private theorem s15_Three_realizes_transport {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B)
    (H : Subgroup (MulAut A)) (H' : Subgroup (MulAut B)) (ρ : ↥H ≃* ↥H')
    (hρ : ∀ (h : ↥H) (a : A), f ((h : MulAut A) a) = ((ρ h : ↥H') : MulAut B) (f a))
    (U : Subgroup A) (hUinv : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut A) u ∈ U)
    (hinj : ∀ u ∈ U, f u = 1 → u = 1) (M₃ : FFModel)
    (hM : M₃.Realizes H' (U.map f) ⊥) : M₃.Realizes H U ⊥ := by
  obtain ⟨π', hπ'⟩ := hM
  obtain ⟨hsurj', -, hker', hUinv', -, hsec, hker, β', hβ'surj, hβ'ker, hβ'intw⟩ := hπ'
  refine ⟨MonoidHom.comp ρ.symm.toMonoidHom π', ?_, bot_le, hker', hUinv, ?_, hsec, hker, ?_⟩
  · exact ρ.symm.surjective.comp hsurj'
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · let fU : ↥U →* ↥(U.map f) :=
      (f.comp U.subtype).codRestrict (U.map f) (fun u => Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩)
    have hβ'1 : ∀ x : ↥(U.map f), β' x = 1 ↔ x = 1 := fun x => by
      rw [hβ'ker x]
      constructor
      · intro hx; exact Subtype.ext (Subgroup.mem_bot.mp hx)
      · intro hx; rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp hx
    refine ⟨β'.comp fU, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := hβ'surj y
      obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      refine ⟨⟨u, hu⟩, ?_⟩
      show β' (fU ⟨u, hu⟩) = y
      have hfux : fU ⟨u, hu⟩ = x := Subtype.ext hux
      rw [hfux, hx]
    · intro u
      rw [Subgroup.mem_bot]
      constructor
      · intro h
        have h1 : fU u = 1 := (hβ'1 (fU u)).1 h
        refine hinj (u : A) u.2 ?_
        have h2 : (fU u : B) = 1 := Subtype.ext_iff.mp h1
        rwa [show (fU u : B) = f (u : A) from rfl] at h2
      · intro h
        rw [show u = 1 from Subtype.ext h]
        exact map_one (β'.comp fU)
    · intro γ u m hu hm hβu
      have hu' : ((π' γ : ↥H') : MulAut B) (f (u : A)) ∈ U.map f := by
        have htmp := hρ (ρ.symm (π' γ)) (u : A)
        rw [MulEquiv.apply_symm_apply] at htmp
        rw [← htmp]
        exact Subgroup.mem_map.mpr ⟨((ρ.symm (π' γ) : ↥H) : MulAut A) (u : A), hu, rfl⟩
      have hfU : fU ⟨((ρ.symm (π' γ) : ↥H) : MulAut A) (u : A), hu⟩ =
          ⟨((π' γ : ↥H') : MulAut B) (f (u : A)), hu'⟩ := by
        refine Subtype.ext ?_
        show f (((ρ.symm (π' γ) : ↥H) : MulAut A) (u : A)) =
          ((π' γ : ↥H') : MulAut B) (f (u : A))
        rw [hρ, MulEquiv.apply_symm_apply]
      have hβ'u : β' (fU u) = QuotientGroup.mk m := hβu
      change β' (fU ⟨((ρ.symm (π' γ) : ↥H) : MulAut A) (u : A), hu⟩) =
        QuotientGroup.mk ⟨M₃.act γ (m : M₃.Amb), hm⟩
      rw [hfU]
      exact hβ'intw γ (fU u) m hu' hm hβ'u

private theorem s15_Three_commSub_stable {A : Type*} [CommGroup A] (K : Subgroup (MulAut A)) :
    ∀ h : ↥K, ∀ u ∈ commSub (⊤ : Subgroup A) K, (h : MulAut A) u ∈ commSub ⊤ K := by
  intro h u hu
  rw [commSub] at hu ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro c ⟨x, hx, w, -, rfl⟩
    refine Subgroup.subset_closure ⟨(h : MulAut A) * x * (h : MulAut A)⁻¹, ?_,
      (h : MulAut A) w, trivial, ?_⟩
    · exact K.mul_mem (K.mul_mem h.2 hx) (K.inv_mem h.2)
    · rw [MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv]
      rw [show ((h : MulAut A)⁻¹) ((h : MulAut A) w) = w from
        MulEquiv.symm_apply_apply _ _]
  · simp
  · intro x y hx hy ihx ihy
    rw [map_mul]
    exact (commSub ⊤ K).mul_mem ihx ihy
  · intro x hx ihx
    rw [map_inv]
    exact (commSub ⊤ K).inv_mem ihx

private theorem s15_Three_commSub_map {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B)
    (H : Subgroup (MulAut A)) (H' : Subgroup (MulAut B)) (ρ : ↥H ≃* ↥H')
    (hρ : ∀ (h : ↥H) (a : A), f ((h : MulAut A) a) = ((ρ h : ↥H') : MulAut B) (f a))
    (hsurj : Function.Surjective f) :
    (commSub (⊤ : Subgroup A) H).map f = commSub ⊤ H' := by
  apply le_antisymm
  · rw [commSub, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    change f (x w * w⁻¹) ∈ commSub ⊤ H'
    rw [map_mul, map_inv, hρ ⟨x, hx⟩ w]
    exact Subgroup.subset_closure ⟨ρ ⟨x, hx⟩, (ρ ⟨x, hx⟩).2, f w, trivial, rfl⟩
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    obtain ⟨w₀, rfl⟩ := hsurj w
    refine Subgroup.mem_map.mpr ⟨(ρ.symm ⟨x, hx⟩ : MulAut A) w₀ * w₀⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure
        ⟨(ρ.symm ⟨x, hx⟩ : ↥H), (ρ.symm ⟨x, hx⟩).2, w₀, trivial, rfl⟩
    · rw [map_mul, map_inv, hρ (ρ.symm ⟨x, hx⟩) w₀, MulEquiv.apply_symm_apply]

private theorem s15_Three_commSub_fix_trivial {A : Type*} [CommGroup A] (hA : ∀ a : A, a ^ 2 = 1)
    (t : MulAut A) (ht : t ^ 3 = 1) :
    ∀ c ∈ commSub (⊤ : Subgroup A) (Subgroup.zpowers t), t c = c → c = 1 := by
  let N : A →* A := MonoidHom.id A * t.toMonoidHom * (t ^ 2).toMonoidHom
  have hN_apply : ∀ a, N a = a * t a * (t ^ 2) a := by
    intro a
    simp only [N, MonoidHom.mul_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
  have hNt : ∀ a, N (t a) = N a := by
    intro a
    rw [hN_apply, hN_apply]
    have h1 : t (t a) = (t ^ 2) a := by rw [pow_two, MulAut.mul_apply]
    have h2 : (t ^ 2) (t a) = a := by
      have hmul : t ^ 2 * t = t ^ 3 := (pow_succ t 2).symm
      rw [← MulAut.mul_apply, hmul, ht, MulAut.one_apply]
    rw [h1, h2]
    ac_rfl
  let H : Subgroup (MulAut A) :=
    { carrier := {x | ∀ a, N (x a) = N a}
      one_mem' := by intro a; rw [MulAut.one_apply]
      mul_mem' := by intro x y hx hy a; rw [MulAut.mul_apply, hx (y a), hy a]
      inv_mem' := by
        intro x hx a
        have h := hx (x⁻¹ a)
        simpa [MulEquiv.apply_symm_apply] using h.symm }
  have hzH : Subgroup.zpowers t ≤ H := Subgroup.zpowers_le.mpr hNt
  have hNzpow : ∀ k : ℤ, ∀ a, N ((t ^ k) a) = N a := by
    intro k a
    exact hzH (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩) a
  have hkill : ∀ c ∈ commSub (⊤ : Subgroup A) (Subgroup.zpowers t), N c = 1 := by
    intro c hc
    rw [commSub] at hc
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hc
    · rintro c ⟨x, hx, w, -, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [map_mul, map_inv, hNzpow k w]
      simp
    · exact map_one N
    · intro x y hx hy ihx ihy
      rw [map_mul, ihx, ihy, one_mul]
    · intro x hx ihx
      rw [map_inv, ihx, inv_one]
  intro c hc hfix
  have hNc : N c = 1 := hkill c hc
  have h2 : N c = c := by
    rw [hN_apply, hfix]
    have ht2 : (t ^ 2) c = c := by
      rw [show (t ^ 2) c = t (t c) from by rw [pow_two, MulAut.mul_apply], hfix, hfix]
    rw [ht2]
    show c * c * c = c
    rw [← pow_two, hA c, one_mul]
  rw [h2] at hNc
  exact hNc

private theorem s15_Three_centralizes_v1 (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hV0 : V₀ = ⊥) : ∀ k ∈ L, ∀ x ∈ v1Sub D.M V₀ V hV L, k * x * k⁻¹ = x := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hV0mem : ∀ e : G, e ∈ V₀ → e = 1 := by
    intro e he
    rw [hV0] at he
    exact Subgroup.mem_bot.mp he
  intro k hk x hx
  set W : Subgroup G := wSub V₀ V hV L ⊓ centralizer (L : Set G) with hW
  have hV1 : v1Sub D.M V₀ V hV L = ⨆ m : D.M, conjSubgroup W (m : G) := by
    rw [v1Sub_of_eq_bot D.M V₀ V hV L hV0, ← hW]
  rw [hV1] at hx
  rw [Subgroup.iSup_eq_closure] at hx
  have hbase : ∀ (m : G) (hm : m ∈ D.M) (w : G), w ∈ W →
      (m * k * m⁻¹) * w * (m * k * m⁻¹)⁻¹ = w := by
    intro m hm w hw
    have hwV : w ∈ V := preTil_le V₀ V hV (wTil V₀ V hV L) hw.1
    set c : G := m * k * m⁻¹ with hc
    have hcM : c ∈ D.M := D.M.mul_mem (D.M.mul_mem hm (h.le hk)) (D.M.inv_mem hm)
    have hcstab : c ∈ stabTil V₀ V := hMs hcM
    by_cases hmn : m ∈ nBar D.M V₀ V hV L
    · obtain ⟨-, hst, hnorm⟩ := (s15_Three_mem_nBar (D := D) (V₀ := V₀) (V := V) (L := L)
        hV).1 hmn
      have hkbar : actTil V₀ V hV ⟨k, hMs (h.le hk)⟩ ∈ barSub V₀ V hV L :=
        actTil_mem_barSub V₀ V hV hk (hMs (h.le hk))
      have hmem : actTil V₀ V hV ⟨c, hcstab⟩ ∈ barSub V₀ V hV L := by
        have hsub : (⟨c, hcstab⟩ : stabTil V₀ V) =
            (⟨m, hst⟩ : stabTil V₀ V) * ⟨k, hMs (h.le hk)⟩ *
              (⟨m, hst⟩ : stabTil V₀ V)⁻¹ := by
          apply Subtype.ext
          show c = m * k * m⁻¹
          rfl
        rw [hsub, map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hnorm
          (actTil V₀ V hV ⟨k, hMs (h.le hk)⟩)).mp hkbar
      obtain ⟨l', hl'L, hl'eq⟩ := (mem_barSub V₀ V hV L _).1 hmem
      have hg1 : actTil V₀ V hV ((⟨c, hcstab⟩ : stabTil V₀ V) * l'⁻¹) = 1 := by
        rw [map_mul, map_inv, hl'eq, mul_inv_cancel]
      have hl'w : (l' : G) * w * (l' : G)⁻¹ = w := by
        have hcl := Subgroup.mem_centralizer_iff.mp hw.2 (l' : G) hl'L
        calc (l' : G) * w * (l' : G)⁻¹ = (w * (l' : G)) * (l' : G)⁻¹ := by rw [hcl]
          _ = w := by group
      have hfixc : (c * (l' : G)⁻¹) * w * (c * (l' : G)⁻¹)⁻¹ = w := by
        have h0 := (actTil_eq_one_iff V₀ V hV
          ((⟨c, hcstab⟩ : stabTil V₀ V) * l'⁻¹)).1 hg1 w hwV
        have h0' : (↑((⟨c, hcstab⟩ : stabTil V₀ V) * l'⁻¹) * w *
            (↑((⟨c, hcstab⟩ : stabTil V₀ V) * l'⁻¹))⁻¹) * w⁻¹ = 1 := hV0mem _ h0
        have h0'' : ↑((⟨c, hcstab⟩ : stabTil V₀ V) * l'⁻¹) * w *
            (↑((⟨c, hcstab⟩ : stabTil V₀ V) * l'⁻¹))⁻¹ = w := mul_inv_eq_one.mp h0'
        simpa using h0''
      have hdecomp : c = (c * (l' : G)⁻¹) * (l' : G) := by group
      rw [hdecomp]
      calc ((c * (l' : G)⁻¹) * (l' : G)) * w * ((c * (l' : G)⁻¹) * (l' : G))⁻¹
          = (c * (l' : G)⁻¹) * ((l' : G) * w * (l' : G)⁻¹) *
              (c * (l' : G)⁻¹)⁻¹ := by group
        _ = (c * (l' : G)⁻¹) * w * (c * (l' : G)⁻¹)⁻¹ := by rw [hl'w]
        _ = w := hfixc
    · have hmn' : m⁻¹ ∉ nBar D.M V₀ V hV L := by
        intro hmem
        exact hmn (by simpa using (nBar D.M V₀ V hV L).inv_mem hmem)
      have hcomm := (h.commute m⁻¹ (D.M.inv_mem hm) hmn').2
      have hc_conj : c ∈ conjSubgroup L m⁻¹ := by
        rw [mem_conjSubgroup_iff]
        rw [show (m⁻¹) * c * (m⁻¹)⁻¹ = k by rw [hc]; group]
        exact hk
      have hcbar : actTil V₀ V hV ⟨c, hcstab⟩ ∈ barSub V₀ V hV (conjSubgroup L m⁻¹) :=
        actTil_mem_barSub V₀ V hV hc_conj hcstab
      have hwt : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ wTil V₀ V hV L :=
        (mem_preTil_iff_of_mem V₀ V hV (wTil V₀ V hV L) hwV).1 hw.1
      have hfix := ((commSub_eq_bot_iff.mp hcomm) hwt)
        (actTil V₀ V hV ⟨c, hcstab⟩) hcbar
      rw [actTil_mk] at hfix
      rw [mkTil_eq_iff] at hfix
      have hfix' : (actStab V₀ V hV ⟨c, hcstab⟩ (IntMod.mk hV ⟨w, hwV⟩)).val *
          (IntMod.mk hV ⟨w, hwV⟩).val⁻¹ = 1 := hV0mem _ hfix
      rw [mul_inv_eq_one, actStab_apply_val] at hfix'
      exact hfix'
  have hgen : ∀ y ∈ ⋃ m : D.M, (conjSubgroup W (m : G) : Set G), k * y * k⁻¹ = y := by
    intro y hy
    obtain ⟨m, hy⟩ := Set.mem_iUnion.mp hy
    have hm : (m : G) ∈ D.M := m.2
    have hw : (m : G) * y * (m : G)⁻¹ ∈ W := mem_conjSubgroup_iff.mp hy
    calc k * y * k⁻¹
        = (m : G)⁻¹ * (((m : G) * k * (m : G)⁻¹) * ((m : G) * y * (m : G)⁻¹)
            * ((m : G) * k * (m : G)⁻¹)⁻¹) * (m : G) := by group
      _ = (m : G)⁻¹ * ((m : G) * y * (m : G)⁻¹) * (m : G) := by
            rw [hbase (m : G) hm ((m : G) * y * (m : G)⁻¹) hw]
      _ = y := by group
  refine Subgroup.closure_induction hgen ?_ ?_ ?_ hx
  · group
  · intro y z hy hz ihy ihz
    calc k * (y * z) * k⁻¹ = (k * y * k⁻¹) * (k * z * k⁻¹) := by group
      _ = y * z := by rw [ihy, ihz]
  · intro y hy ihy
    calc k * y⁻¹ * k⁻¹ = (k * y * k⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [ihy]

private theorem s15_Three_equiv_star (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hK : K₀ ≤ D.M) (hV0 : V₀ = ⊥) :
    ∃ (f : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV)
      (ρ : ↥(barSub V₀ V hV K₀) ≃* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)),
      (∀ x : IntMod V hV, f (mkTil V₀ V hV x) =
        mkTil (v1Sub D.M V₀ V hV L) V hV x) ∧
      ∀ (a : ↥(barSub V₀ V hV K₀)) (y : Vtil V₀ V hV),
        f ((a : MulAut (Vtil V₀ V hV)) y) =
          ((ρ a : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
            MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f y) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub (L := L) h.hyp125 hV)
  have hle : V₀ ≤ v1Sub D.M V₀ V hV L := by rw [hV0]; exact bot_le
  let f : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV :=
    QuotientGroup.map (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV)
      (MonoidHom.id (IntMod V hV)) (by
        rw [Subgroup.comap_id]
        intro x hx
        rw [mem_modNull] at hx ⊢
        exact hle hx)
  have hf : ∀ x : IntMod V hV, f (mkTil V₀ V hV x) =
      mkTil (v1Sub D.M V₀ V hV L) V hV x := by
    intro x
    exact QuotientGroup.map_mk (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV)
      (MonoidHom.id (IntMod V hV)) _ x
  let σ₀ : ↥K₀ →* ↥(barSub V₀ V hV K₀) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion (hK.trans hMs))).codRestrict _
      (fun k => by
        change actTil V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ ∈ barSub V₀ V hV K₀
        exact actTil_mem_barSub V₀ V hV k.2 (hMs (hK k.2)))
  let σ₁ : ↥K₀ →* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) :=
    ((actTil (v1Sub D.M V₀ V hV L) V hV).comp (Subgroup.inclusion (hK.trans hMs1))).codRestrict _
      (fun k => by
        change actTil (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ ∈
          barSub (v1Sub D.M V₀ V hV L) V hV K₀
        exact actTil_mem_barSub _ V hV k.2 (hMs1 (hK k.2)))
  have hσ₀val : ∀ k : ↥K₀, (σ₀ k : MulAut (Vtil V₀ V hV)) =
      actTil V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ := fun k =>
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)
  have hσ₁val : ∀ k : ↥K₀,
      (σ₁ k : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) =
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ := fun k =>
    congrArg (actTil _ V hV) (Subtype.ext rfl)
  have hσ₀ : Function.Surjective σ₀ := by
    intro a
    obtain ⟨g, hgK, hga⟩ := (mem_barSub V₀ V hV K₀ a).1 a.2
    refine ⟨⟨(g : G), hgK⟩, ?_⟩
    apply Subtype.ext
    rw [hσ₀val ⟨(g : G), hgK⟩]
    rw [show actTil V₀ V hV ⟨(g : G), hMs (hK hgK)⟩ = actTil V₀ V hV g from
      congrArg _ (Subtype.ext rfl)]
    exact hga
  have hσ₁ : Function.Surjective σ₁ := by
    intro a
    obtain ⟨g, hgK, hga⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV K₀ a).1 a.2
    refine ⟨⟨(g : G), hgK⟩, ?_⟩
    apply Subtype.ext
    rw [hσ₁val ⟨(g : G), hgK⟩]
    rw [show actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), hMs1 (hK hgK)⟩ =
        actTil (v1Sub D.M V₀ V hV L) V hV g from congrArg _ (Subtype.ext rfl)]
    exact hga
  have hker₀ : σ₀.ker = (F11.CTilde D.M V₀ V).subgroupOf K₀ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hk
      have h3 := congrArg (fun z : ↥(barSub V₀ V hV K₀) =>
        (z : MulAut (Vtil V₀ V hV))) hk
      rw [hσ₀val k] at h3
      exact ⟨hK k.2, hMs (hK k.2), by simpa using h3⟩
    · rintro ⟨-, hst, hact⟩
      apply Subtype.ext
      rw [hσ₀val k]
      rw [show (⟨(k : G), hMs (hK k.2)⟩ : stabTil V₀ V) = ⟨(k : G), hst⟩ from
        Subtype.ext rfl]
      exact hact
  have hker₁ : σ₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer]
    constructor
    · intro hk
      have h3 := congrArg (fun z : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) =>
        (z : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))) hk
      rw [hσ₁val k] at h3
      exact ⟨hK k.2, hMs1 (hK k.2), by simpa using h3⟩
    · rintro ⟨-, hst, hact⟩
      apply Subtype.ext
      rw [hσ₁val k]
      rw [show (⟨(k : G), hMs1 (hK k.2)⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
          ⟨(k : G), hst⟩ from Subtype.ext rfl]
      exact hact
  have hkereq : (F11.CTilde D.M V₀ V).subgroupOf K₀ =
      (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀ := by
    rw [fifteen_two_cent D h1217 h hV]
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf K₀).Normal := hker₀ ▸ MonoidHom.normal_ker σ₀
  haveI : ((F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀).Normal :=
    hker₁ ▸ MonoidHom.normal_ker σ₁
  let e0 : ↥K₀ ⧸ (F11.CTilde D.M V₀ V).subgroupOf K₀ ≃* ↥(barSub V₀ V hV K₀) :=
    QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf K₀) hσ₀ hker₀.symm
  let e1 : ↥K₀ ⧸ (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀ ≃*
      ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) :=
    QuotientGroup.liftEquiv ((F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf K₀)
      hσ₁ hker₁.symm
  let ρ : ↥(barSub V₀ V hV K₀) ≃* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀) :=
    e0.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkereq).trans e1)
  have hρk : ∀ k : ↥K₀, ρ (σ₀ k) = σ₁ k := by
    intro k
    have h0 : e0.symm (σ₀ k) = QuotientGroup.mk k := by
      rw [show σ₀ k = e0 (QuotientGroup.mk k) from
        (QuotientGroup.liftEquiv_mk _ hσ₀ hker₀.symm k).symm]
      exact MulEquiv.symm_apply_apply e0 _
    have h1 : (QuotientGroup.quotientMulEquivOfEq hkereq) (QuotientGroup.mk k) =
        QuotientGroup.mk k := QuotientGroup.quotientMulEquivOfEq_mk hkereq k
    have h2 : e1 (QuotientGroup.mk k) = σ₁ k :=
      QuotientGroup.liftEquiv_mk _ hσ₁ hker₁.symm k
    change e1 ((QuotientGroup.quotientMulEquivOfEq hkereq) (e0.symm (σ₀ k))) = σ₁ k
    rw [h0, h1, h2]
  have hstab : ∀ (k : ↥K₀) (x : IntMod V hV),
      actStab V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ x =
        actStab (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ x := by
    intro k x
    apply IntMod.val_injective
    rw [actStab_apply_val, actStab_apply_val]
  have hσinter : ∀ (k : ↥K₀) (y : Vtil V₀ V hV),
      f ((σ₀ k : MulAut (Vtil V₀ V hV)) y) =
        ((σ₁ k : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
          MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f y) := by
    intro k y
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV y
    have hL : f ((σ₀ k : MulAut (Vtil V₀ V hV)) (mkTil V₀ V hV x)) =
        mkTil (v1Sub D.M V₀ V hV L) V hV
          (actStab V₀ V hV ⟨(k : G), hMs (hK k.2)⟩ x) := by
      rw [hσ₀val k, actTil_mk, hf]
    have hR : ((σ₁ k : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
          MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f (mkTil V₀ V hV x)) =
        mkTil (v1Sub D.M V₀ V hV L) V hV
          (actStab (v1Sub D.M V₀ V hV L) V hV ⟨(k : G), hMs1 (hK k.2)⟩ x) := by
      rw [hσ₁val k, hf, actTil_mk]
    rw [hL, hR, hstab k x]
  refine ⟨f, ρ, hf, ?_⟩
  intro a y
  obtain ⟨k, rfl⟩ := hσ₀ a
  rw [hρk k]
  exact hσinter k y

private theorem s15_Three_Z3_inj (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3)
    (hV0 : V₀ = ⊥) (f : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV)
    (hf : ∀ x : IntMod V hV, f (mkTil V₀ V hV x) =
      mkTil (v1Sub D.M V₀ V hV L) V hV x) :
    ∀ u ∈ commSub ⊤ (barSub V₀ V hV K₀), f u = 1 → u = 1 := by
  have hV0mem' : ∀ e : G, e = 1 → e ∈ V₀ := by
    intro e he
    rw [hV0, he]
    exact Subgroup.one_mem _
  haveI : IsCyclic ↥(barSub V₀ V hV K₀) := hZ.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(barSub V₀ V hV K₀))
  let t : MulAut (Vtil V₀ V hV) := (g : MulAut (Vtil V₀ V hV))
  have hgen : barSub V₀ V hV K₀ = Subgroup.zpowers t := by
    have htop : (⊤ : Subgroup ↥(barSub V₀ V hV K₀)) = Subgroup.zpowers g := by
      refine le_antisymm ?_ le_top
      intro x _
      exact hg x
    have hmap : Subgroup.map (Subgroup.subtype (barSub V₀ V hV K₀)) ⊤ =
        barSub V₀ V hV K₀ := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap, htop, MonoidHom.map_zpowers]
    rfl
  have ht3 : t ^ 3 = 1 := by
    have hg3 : g ^ 3 = 1 := by
      have := pow_card_eq_one' (x := g)
      rwa [hZ.2] at this
    have := congrArg (Subgroup.subtype (barSub V₀ V hV K₀)) hg3
    simpa using this
  obtain ⟨c, hcK, hct⟩ := (mem_barSub V₀ V hV K₀ t).1 g.2
  intro u hu hfu
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV u
  have hxV₁ : x.val ∈ v1Sub D.M V₀ V hV L := by
    have h1 : mkTil (v1Sub D.M V₀ V hV L) V hV x = 1 := by
      rw [← hf x]; exact hfu
    have h2 : mkTil (v1Sub D.M V₀ V hV L) V hV x =
        mkTil (v1Sub D.M V₀ V hV L) V hV 1 := by rw [h1, map_one]
    have h3 := (mkTil_eq_iff (v1Sub D.M V₀ V hV L) V hV x 1).1 h2
    simpa using h3
  have htu : t (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
    rw [← hct, actTil_mk]
    apply (mkTil_eq_iff V₀ V hV (actStab V₀ V hV c x) x).2
    apply hV0mem'
    rw [actStab_apply_val,
      s15_Three_centralizes_v1 h hV hV0 (c : G) (hshape.1 hcK) x.val hxV₁, mul_inv_cancel]
  have hu' : mkTil V₀ V hV x ∈ commSub ⊤ (Subgroup.zpowers t) := by
    rw [← hgen]; exact hu
  exact s15_Three_commSub_fix_trivial (s15_Infra_vtil_sq_eq_one V₀ V hV) t ht3
    (mkTil V₀ V hV x) hu' htu

private theorem s15_Three_Z3_natural_bot_gap (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3) (hV0 : V₀ = ⊥) :
    ∃ (f : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV)
      (ρ : ↥(barSub V₀ V hV K₀) ≃* ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)),
      (∀ x : IntMod V hV, f (mkTil V₀ V hV x) =
        mkTil (v1Sub D.M V₀ V hV L) V hV x) ∧
      (∀ (a : ↥(barSub V₀ V hV K₀)) (y : Vtil V₀ V hV),
        f ((a : MulAut (Vtil V₀ V hV)) y) =
          ((ρ a : ↥(barSub (v1Sub D.M V₀ V hV L) V hV K₀)) :
            MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) (f y)) ∧
      (∀ u ∈ commSub ⊤ (barSub V₀ V hV K₀), f u = 1 → u = 1) := by
  have hK : K₀ ≤ D.M := hshape.1.trans h.le
  obtain ⟨f, ρ, hf, hρ⟩ := s15_Three_equiv_star h1217 h hV hK hV0
  exact ⟨f, ρ, hf, hρ, s15_Three_Z3_inj h hV hshape hZ hV0 f hf⟩

theorem s15_Three_Z3_natural_bot (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3) (hV0 : V₀ = ⊥)
    (hnat : AlternatingNatural (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 3) :
    AlternatingNatural (barSub V₀ V hV K₀) (commSub ⊤ (barSub V₀ V hV K₀)) ⊥ 3 := by
  obtain ⟨f, ρ, hf, hρ, hinj⟩ :=
    s15_Three_Z3_natural_bot_gap h1217 h hV hshape hZ hV0
  have hsurj : Function.Surjective f := fun b => by
    obtain ⟨x, rfl⟩ := mkTil_surjective (v1Sub D.M V₀ V hV L) V hV b
    exact ⟨mkTil V₀ V hV x, hf x⟩
  have hmap := s15_Three_commSub_map f (barSub V₀ V hV K₀)
    (barSub (v1Sub D.M V₀ V hV L) V hV K₀) ρ hρ hsurj
  have hinv := s15_Three_commSub_stable (barSub V₀ V hV K₀)
  rw [AlternatingNatural] at hnat ⊢
  rw [← hmap] at hnat
  exact s15_Three_realizes_transport f (barSub V₀ V hV K₀)
    (barSub (v1Sub D.M V₀ V hV L) V hV K₀) ρ hρ
    (commSub ⊤ (barSub V₀ V hV K₀)) hinv hinj (FFModel.altDn 3) hnat

theorem s15_Three_Z3_natural (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3)
    (hnat : AlternatingNatural (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 3) :
    AlternatingNatural (barSub V₀ V hV K₀) (commSub ⊤ (barSub V₀ V hV K₀)) ⊥ 3 := by
  by_cases hV0 : V₀ = ⊥
  · exact s15_Three_Z3_natural_bot h1217 h hV hshape hZ hV0 hnat
  · have e : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV0
    rw [e] at hnat
    exact hnat

private theorem s15_Three_le_stabTilZ3 {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) : D.M ≤ stabTil V₀ V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀

private theorem s15_Three_closure_elemAbelian {A : Type*} [Group A] {k : Set A} {p : ℕ}
    (hpair : k.Pairwise Commute) (hexp : ∀ x ∈ k, x ^ p = 1) :
    IsElemAbelian p (Subgroup.closure k) := by
  haveI : IsMulCommutative ↥(Subgroup.closure k) := Subgroup.isMulCommutative_closure hpair
  refine ⟨inferInstance, ?_⟩
  have hcomm : ∀ x ∈ Subgroup.closure k, ∀ y ∈ Subgroup.closure k, x * y = y * x :=
    fun x hx y hy =>
      congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x, hx⟩ : ↥(Subgroup.closure k)) ⟨y, hy⟩)
  intro x hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · exact fun y hy => hexp y hy
  · simp
  · intro y z hy hz ihy ihz
    rw [Commute.mul_pow (hcomm y hy z hz), ihy, ihz, one_mul]
  · intro y hy ihy
    rw [inv_pow, ihy, inv_one]

private theorem s15_Three_barSub_elemAbelian_three {D : Data G} {V₀ V K₀ : Subgroup G}
    {hV : IsElemAbelian 2 V} (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3) :
    IsElemAbelian 3 (barSub V₀ V hV K₀) := by
  haveI : IsCyclic ↥(barSub V₀ V hV K₀) := hZ.1
  refine ⟨inferInstance, ?_⟩
  intro x hx
  have hpow : (⟨x, hx⟩ : ↥(barSub V₀ V hV K₀)) ^ Nat.card ↥(barSub V₀ V hV K₀) = 1 :=
    pow_card_eq_one'
  have hval : x ^ Nat.card ↥(barSub V₀ V hV K₀) = 1 := by
    have h2 := congrArg (barSub V₀ V hV K₀).subtype hpow
    rw [map_pow] at h2
    simpa using h2
  simpa [hZ.2] using hval

private theorem s15_Three_conjElemAbelian {D : Data G} {V₀ V L K₀ : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3)
    {m : G} (hm : m ∈ D.M) :
    IsElemAbelian 3 (barSub V₀ V hV (conjSubgroup K₀ m)) := by
  rw [s15_Three_barSub_conj_eq hV (s15_Three_le_stabTilZ3 h) (hshape.1.trans h.le) hm]
  exact (s15_Three_barSub_elemAbelian_three (D := D) (V₀ := V₀) (V := V) (K₀ := K₀) hZ).map _

private theorem s15_Three_xbar_elemAbelian {D : Data G} {V₀ V L K₀ : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3) :
    IsElemAbelian 3 (s15XBar D V₀ V hV K₀) := by
  set T : Set (MulAut (Vtil V₀ V hV)) :=
    ⋃ m ∈ D.M, (barSub V₀ V hV (conjSubgroup K₀ m) : Set (MulAut (Vtil V₀ V hV))) with hT
  have hXeq : s15XBar D V₀ V hV K₀ = Subgroup.closure T := by
    apply le_antisymm
    · rw [s15XBar]
      refine iSup₂_le fun m hm => fun x hx => Subgroup.subset_closure ?_
      rw [hT]
      exact Set.mem_iUnion₂.mpr ⟨m, hm, hx⟩
    · rw [s15XBar]
      rw [Subgroup.closure_le]
      intro x hx
      rw [hT] at hx
      obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.mp hx
      exact Subgroup.mem_iSup_of_mem m (Subgroup.mem_iSup_of_mem hm hxm)
  rw [hXeq]
  refine s15_Three_closure_elemAbelian ?_ ?_
  · intro a ha b hb _
    rw [hT] at ha hb
    obtain ⟨m₁, hm₁, ha₁⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨m₂, hm₂, hb₂⟩ := Set.mem_iUnion₂.mp hb
    rcases s15_Three_xbar_comm (D := D) h hV hshape hm₁ hm₂ with heq | hcomm
    · haveI : IsMulCommutative ↥(barSub V₀ V hV (conjSubgroup K₀ m₂)) :=
        (s15_Three_conjElemAbelian h hV hshape hZ hm₂).1
      rw [heq] at ha₁
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨a, ha₁⟩ : ↥(barSub V₀ V hV (conjSubgroup K₀ m₂))) ⟨b, hb₂⟩)
    · exact hcomm a ha₁ b hb₂
  · intro x hx
    rw [hT] at hx
    obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.mp hx
    exact (s15_Three_conjElemAbelian h hV hshape hZ hm).2 x hxm

private theorem s15_Three_xbar_le_der {D : Data G} {V₀ V L K₀ : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) :
    s15XBar D V₀ V hV K₀ ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ := by
  set C : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ with hC
  have hCle : C ≤ Mbar D.M V₀ V hV := by
    rw [hC]
    exact (Subgroup.commutator_le_sup (Mbar D.M V₀ V hV) (Mbar D.M V₀ V hV)).trans
      (le_of_eq (sup_idem _))
  have hnorm : (C.subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [hC]
      exact Subgroup.normalizer_commutator_ge_left (Mbar D.M V₀ V hV) (Mbar D.M V₀ V hV))
  have hleNorm : Mbar D.M V₀ V hV ≤ normalizer (C : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCle).1 hnorm
  refine iSup₂_le fun m hm => ?_
  rw [s15_Three_barSub_conj_eq hV (s15_Three_le_stabTilZ3 h) (hshape.1.trans h.le) hm]
  refine Subgroup.map_le_iff_le_comap.2 fun x hx => ?_
  have hφ : actTil V₀ V hV ⟨m⁻¹, s15_Three_le_stabTilZ3 h (D.M.inv_mem hm)⟩ ∈
      normalizer (C : Set (MulAut (Vtil V₀ V hV))) :=
    hleNorm (actTil_mem_barSub V₀ V hV (D.M.inv_mem hm)
      (s15_Three_le_stabTilZ3 h (D.M.inv_mem hm)))
  rw [Subgroup.mem_comap]
  change (MulAut.conj (actTil V₀ V hV ⟨m⁻¹, s15_Three_le_stabTilZ3 h (D.M.inv_mem hm)⟩)) x ∈ C
  rw [MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.1 hφ x).1 (hshape.2.1 hx)

private theorem s15_Three_Xbar_transport (hTen : RTenP153 D) (h127 : R127 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 < n)
    (Xb : Subgroup (MulAut (Vtil V₀ V hV))) (hXM : Xb ≤ Mbar D.M V₀ V hV)
    (hN : (Xb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hE : IsElemAbelian p Xb)
    (hcard : Nat.card Xb = p ^ n)
    (hder : Xb ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆) : Nat.card V₀ < 8 := by
  have hMs := s15_Three_le_stabTilZ3 h
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal (D := D) hV hMs
  obtain ⟨e, -⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  set Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (Xb.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom with hXbar
  have hXbarN : Xbar.Normal := by
    rw [hXbar]
    exact hN.map e.symm.toMonoidHom e.symm.surjective
  have hXbarE : IsElemAbelian p Xbar := by
    rw [hXbar]
    exact (hE.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom
  have hcardM : Nat.card (Xb.subgroupOf (Mbar D.M V₀ V hV)) = Nat.card Xb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hcardXb : Nat.card Xbar = Nat.card (Xb.subgroupOf (Mbar D.M V₀ V hV)) := by
    rw [hXbar]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (Xb.subgroupOf (Mbar D.M V₀ V hV))
      e.symm.toMonoidHom e.symm.injective).toEquiv).symm
  have hXbarCard : Nat.card Xbar = p ^ n := by rw [hcardXb, hcardM, hcard]
  have hXbMder : Xb.subgroupOf (Mbar D.M V₀ V hV) ≤ _root_.commutator ↥(Mbar D.M V₀ V hV) := by
    rw [← Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective (Mbar D.M V₀ V hV))]
    rw [Subgroup.map_subgroupOf_eq_of_le hXM, Subgroup.map_subtype_commutator]
    exact hder
  have hXbarDer : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [hXbar]
    refine (Subgroup.map_mono hXbMder).trans_eq ?_
    rw [show _root_.commutator ↥(Mbar D.M V₀ V hV) =
          ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)), ⊤⁆ from rfl,
        Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr e.symm.surjective]
  exact hTen V₀ V hH11 p hp hp2 n hn Xbar hXbarN hXbarE hXbarCard hXbarDer

theorem s15_Three_Z3_rs_one (hTen : RTenP153 D) (h127 : R127 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hZ : IsCyclicOrd ↥(barSub V₀ V hV K₀) 3) (hbig : 2 < mSub V₀) :
    s15Rs D V₀ V hV L K₀ = 1 := by
  have hXbarEA := s15_Three_xbar_elemAbelian h hV hshape hZ
  have hXbarM := s15_Three_xbar_le h hV hshape
  have hXbarN := s15_Three_xbar_normal h hV hshape
  have hXbarDer := s15_Three_xbar_le_der h hV hshape
  have hKbar_le : barSub V₀ V hV K₀ ≤ s15XBar D V₀ V hV K₀ := by
    have h1 : barSub V₀ V hV (conjSubgroup K₀ (1 : G)) = barSub V₀ V hV K₀ := by
      rw [conjSubgroup_one]
    exact le_iSup₂_of_le (1 : G) D.M.one_mem (le_of_eq h1.symm)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3group : IsPGroup 3 ↥(s15XBar D V₀ V hV K₀) := by
    intro x
    refine ⟨1, ?_⟩
    exact Subtype.ext_iff.mpr (hXbarEA.2 (x : MulAut (Vtil V₀ V hV)) x.2)
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq h3group
  have hnpos : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    have hle : Nat.card (barSub V₀ V hV K₀) ≤ Nat.card (s15XBar D V₀ V hV K₀) :=
      Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hKbar_le)
    rw [hZ.2, hn, h0, pow_zero] at hle
    omega
  have hn1 : n = 1 := by
    by_contra hcon
    have hlt : 1 < n := by omega
    have h8 := s15_Three_Xbar_transport hTen h127 h hV Nat.prime_three (by norm_num) hlt
      (Xb := s15XBar D V₀ V hV K₀) hXbarM hXbarN hXbarEA hn hXbarDer
    have hV0_2 : IsPGroup 2 ↥V₀ := fun x => ⟨1, by
      exact Subtype.ext_iff.mpr (h.hyp125.pairFacts.elemAbelian₀.2 (x : G) x.2)⟩
    have hcardV0 : 8 ≤ Nat.card V₀ := by
      rw [card_eq_two_pow_mSub hV0_2]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcardX3 : Nat.card (s15XBar D V₀ V hV K₀) = 3 := by rw [hn, hn1, pow_one]
  have hXeqK : s15XBar D V₀ V hV K₀ = barSub V₀ V hV K₀ :=
    (Subgroup.eq_of_le_of_card_ge hKbar_le (by rw [hcardX3, hZ.2])).symm
  have hKbarM : barSub V₀ V hV K₀ ≤ Mbar D.M V₀ V hV := hXeqK ▸ hXbarM
  have hKbarN : ((barSub V₀ V hV K₀).subgroupOf (Mbar D.M V₀ V hV)).Normal := hXeqK ▸ hXbarN
  have hnorm : Mbar D.M V₀ V hV ≤ normalizer (barSub V₀ V hV K₀ : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKbarM).1 hKbarN
  have hNle : s15NBar D V₀ V hV L ≤ Mbar D.M V₀ V hV := inf_le_left
  have hr : (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard = 1 := by
    have hset : conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) =
        {barSub V₀ V hV K₀} := by
      apply le_antisymm
      · rintro X ⟨n, hnN, rfl⟩
        rw [Set.mem_singleton_iff]
        exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hnorm (hNle hnN))
      · intro X hX
        rw [Set.mem_singleton_iff] at hX
        subst hX
        exact ⟨1, (s15NBar D V₀ V hV L).one_mem, by ext x; simp⟩
    rw [hset, Set.ncard_singleton]
  have hLK' : barSub V₀ V hV L = barSub V₀ V hV K₀ :=
    s15_Three_eq_of_ncard_conjSet hshape.2.2.1 hr
  have hs : s15 D.M V₀ V hV L = 1 := by
    have hsetL : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} =
        {barSub V₀ V hV K₀} := by
      apply le_antisymm
      · rintro X ⟨φ, hφ, rfl⟩
        rw [hLK', Set.mem_singleton_iff]
        exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hnorm hφ)
      · intro X hX
        rw [Set.mem_singleton_iff] at hX
        subst hX
        exact ⟨1, (Mbar D.M V₀ V hV).one_mem, by rw [hLK']; ext x; simp⟩
    unfold s15
    rw [hsetL, Set.ncard_singleton]
  exact (s15_Three_rs_eq_one_iff D V₀ V hV L K₀).2 ⟨hr, hs⟩

theorem s15_Three_card_coreMod_three : Nat.card (G6.coreMod 3) = 4 := by
  show Nat.card {x : G6.PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem s15_Three_altDn3_ker : (FFModel.altDn 3).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 3) ⊓ G6.coreMod 3 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 3 * G6.allOnes 3 = 1 := by decide +kernel
  have hnot : G6.allOnes 3 ∉ G6.coreMod 3 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 3) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

theorem s15_Three_natural_card_Z3 {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {U : Subgroup W} (hnat : AlternatingNatural K U ⊥ 3) : Nat.card U = 4 := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hnat
  have hker : (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec = ⊥ := by
    rw [s15_Three_altDn3_ker, Subgroup.bot_subgroupOf]
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  have hcard1 : Nat.card ↥U = Nat.card (↥(FFModel.altDn 3).sec ⧸
      (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec) :=
    Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
  have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec)
  have hN1 : Nat.card ↥((FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec) = 1 := by
    rw [hker]
    exact Subgroup.card_bot
  have h4 : Nat.card ↥(FFModel.altDn 3).sec = 4 := s15_Three_card_coreMod_three
  rw [h4, hN1, mul_one] at hcard2
  rw [hcard1]
  exact hcard2.symm

theorem s15_Three_rk_tilde (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV0 : V₀ ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀)
    (hrs : s15Rs D V₀ V hV L K₀ = 1)
    (hnat : AlternatingNatural (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 3) :
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 2 := by
  have hs : s15 D.M V₀ V hV L = 1 := ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hrs).2
  have hLK := s15_Three_lBar_eq hshape hrs
  have hstar : lStar D.M V₀ V hV L = barSub (v1Sub D.M V₀ V hV L) V hV K₀ :=
    (s15_Three_barSub_star_iff D h1217 h h.le (hshape.1.trans h.le)).1 hLK
  have hW : commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀) = wStar D.M V₀ V hV L := by
    rw [← hstar]
    exact s15_Three_commSub_top_lStar h hV
  have htop := s15_Three_wStar_eq_top D h1217 h hV hL hs
  have hc := s15_Three_natural_card_Z3 hnat
  rw [hW, htop, Subgroup.card_top] at hc
  change Nat.card (Vtil (v1Sub D.M V₀ V hV L) V hV) = 4 at hc
  rw [v1Sub_of_ne_bot D.M V₀ V hV L hV0] at hc
  show padicValNat 2 (Nat.card ↥(⊤ : Subgroup (Vtil V₀ V hV))) = 2
  rw [Subgroup.card_top, hc, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

theorem s15_Three_case_three (h127 : R127 D) (h1217 : R1217 D) (hTen : RTenP153 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hZ3 : s15KNatZ3 ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀))) : Case153_3 D V₀ V hV L := by
  refine ⟨⟨K₀, hshape.1, hZ3.1, hshape.2.2.1,
    s15_Three_Z3_natural h1217 h hV hshape hZ3.1 hZ3.2⟩, ?_⟩
  by_cases hV0 : mSub V₀ ≤ 2
  · exact Or.inl hV0
  · refine Or.inr ?_
    have hbig : 2 < mSub V₀ := by omega
    have hrs := s15_Three_Z3_rs_one hTen h127 h hV hshape hZ3.1 hbig
    have hne : V₀ ≠ ⊥ := by
      intro h0
      rw [h0] at hbig
      exact absurd hbig (by rw [mSub, rk_bot]; omega)
    exact s15_Three_rk_tilde h1217 h hV hL hne hshape hrs hZ3.2

end CaseThree

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
