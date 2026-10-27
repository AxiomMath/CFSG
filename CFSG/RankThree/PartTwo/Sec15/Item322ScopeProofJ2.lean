module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Perm
public import CFSG.CGT.PushingUpLit.CGT6M.J2Five
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import CFSG.RankThree.PartTwo.Sec3.SectionModuleBound

public section

namespace CFSG.RankThree.PartTwo.Sec15.Item322Scope

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec3

theorem exists_four_conj_closure_eq_top
    {τ : NativeSporadic.J2}
    (hτ : orderOf τ = 2) :
    ∃ c₁ c₂ c₃ c₄ : NativeSporadic.J2,
      Subgroup.closure ({c₁ * τ * c₁⁻¹, c₂ * τ * c₂⁻¹, c₃ * τ * c₃⁻¹, c₄ * τ * c₄⁻¹} :
        Set NativeSporadic.J2) = ⊤ := by
  set φ := CFSG.Sporadic.Schreier.j2PermEquiv with hφ
  set x : Equiv.Perm (Fin 315) := (φ τ : Equiv.Perm (Fin 315)) with hx
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hxR : x ∈ CFSG.Sporadic.SmallOddCore.j2R :=
    CFSG.QuasithinUnique.Bridge.J2Excl.j2P_le_R (φ τ).2
  have hx2 : x ^ 2 = 1 := by
    rw [hx, ← Subgroup.coe_pow, ← map_pow, hτ2, map_one, Subgroup.coe_one]
  have hx1 : x ≠ 1 := fun h => hτ1 (φ.injective (by rw [map_one]; exact Subtype.ext h))
  obtain ⟨gs, hlen, hgs, hle⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_gen4 hxR hx2 hx1
  rcases gs with _ | ⟨g₁, _ | ⟨g₂, _ | ⟨g₃, _ | ⟨g₄, _ | ⟨g₅, gs⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  have m₁ : g₁ ∈ CFSG.Sporadic.Schreier.j2P := hgs g₁ (by simp)
  have m₂ : g₂ ∈ CFSG.Sporadic.Schreier.j2P := hgs g₂ (by simp)
  have m₃ : g₃ ∈ CFSG.Sporadic.Schreier.j2P := hgs g₃ (by simp)
  have m₄ : g₄ ∈ CFSG.Sporadic.Schreier.j2P := hgs g₄ (by simp)
  set f : NativeSporadic.J2 →* Equiv.Perm (Fin 315) :=
    CFSG.Sporadic.Schreier.j2P.subtype.comp
      (φ : NativeSporadic.J2 →* CFSG.Sporadic.Schreier.j2P) with hf
  have hfx : ∀ y : NativeSporadic.J2, f y = (φ y : Equiv.Perm (Fin 315)) := fun y => rfl
  have hfinj : Function.Injective f := fun y z h =>
    φ.injective (Subtype.ext (by rw [← hfx, ← hfx]; exact h))
  have hfc : ∀ (g : Equiv.Perm (Fin 315)) (hg : g ∈ CFSG.Sporadic.Schreier.j2P),
      f (φ.symm ⟨g, hg⟩ * τ * (φ.symm ⟨g, hg⟩)⁻¹) = g * x * g⁻¹ := by
    intro g hg
    rw [hfx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨φ.symm ⟨g₁, m₁⟩, φ.symm ⟨g₂, m₂⟩, φ.symm ⟨g₃, m₃⟩, φ.symm ⟨g₄, m₄⟩, ?_⟩
  rw [eq_top_iff]
  intro y _
  have hy : f y ∈ (Subgroup.closure ({φ.symm ⟨g₁, m₁⟩ * τ * (φ.symm ⟨g₁, m₁⟩)⁻¹,
      φ.symm ⟨g₂, m₂⟩ * τ * (φ.symm ⟨g₂, m₂⟩)⁻¹, φ.symm ⟨g₃, m₃⟩ * τ * (φ.symm ⟨g₃, m₃⟩)⁻¹,
      φ.symm ⟨g₄, m₄⟩ * τ * (φ.symm ⟨g₄, m₄⟩)⁻¹} : Set NativeSporadic.J2)).map f := by
    refine hle.trans ?_ (φ y).2
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨c, hc, t, ht, rfl⟩
    rw [Set.mem_singleton_iff] at ht
    subst ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, hfc _ m₁⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hfc _ m₂⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hfc _ m₃⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), hfc _ m₄⟩
  obtain ⟨s, hs, hsy⟩ := hy
  rw [← hfinj hsy]
  exact hs

theorem exists_four_conj_closure_eq_top_of_equiv
    {Γ : Type*} [Group Γ]
    (e : Γ ≃* NativeSporadic.J2) {τ : Γ} (hτ : orderOf τ = 2) :
    ∃ c₁ c₂ c₃ c₄ : Γ,
      Subgroup.closure ({c₁ * τ * c₁⁻¹, c₂ * τ * c₂⁻¹, c₃ * τ * c₃⁻¹, c₄ * τ * c₄⁻¹} :
        Set Γ) = ⊤ := by
  have hτ' : orderOf (e τ) = 2 := by
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [← map_pow, ← hτ, pow_orderOf_eq_one, map_one]
    · have h1 : τ = 1 := e.injective (by rw [h, map_one])
      rw [h1, orderOf_one] at hτ
      exact absurd hτ (by norm_num)
  obtain ⟨c₁, c₂, c₃, c₄, hgen⟩ := exists_four_conj_closure_eq_top hτ'
  refine ⟨e.symm c₁, e.symm c₂, e.symm c₃, e.symm c₄, ?_⟩
  set ψ : NativeSporadic.J2 →* Γ := (e.symm : NativeSporadic.J2 →* Γ) with hψ
  have hψx : ∀ y : NativeSporadic.J2, ψ y = e.symm y := fun y => rfl
  have hψc : ∀ c : NativeSporadic.J2, ψ (c * e τ * c⁻¹) = e.symm c * τ * (e.symm c)⁻¹ := by
    intro c
    rw [hψx, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [eq_top_iff]
  intro z _
  have hz : ψ (e z) ∈ (Subgroup.closure ({c₁ * e τ * c₁⁻¹, c₂ * e τ * c₂⁻¹, c₃ * e τ * c₃⁻¹,
      c₄ * e τ * c₄⁻¹} : Set NativeSporadic.J2)).map ψ :=
    Subgroup.mem_map_of_mem _ (by rw [hgen]; exact Subgroup.mem_top _)
  rw [hψx, MulEquiv.symm_apply_apply, MonoidHom.map_closure] at hz
  refine Subgroup.closure_mono ?_ hz
  rintro _ ⟨c, hc, rfl⟩
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl (hψc c₁)
  · exact Or.inr (Or.inl (hψc c₂))
  · exact Or.inr (Or.inr (Or.inl (hψc c₃)))
  · exact Or.inr (Or.inr (Or.inr (hψc c₄)))

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_top_of_forall_mk {Q : Subgroup X} [Q.Normal] {H : Subgroup X} (hQH : Q ≤ H)
    (h : ∀ x : X, ∃ y ∈ H, QuotientGroup.mk' Q y = QuotientGroup.mk' Q x) : H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := h x
  have h2 : y⁻¹ * x ∈ Q := QuotientGroup.eq.mp hyx
  have e3 : x = y * (y⁻¹ * x) := by group
  rw [e3]
  exact H.mul_mem hy (hQH h2)

omit [Finite X] in
theorem le_or_eq_top_of_normal {Q : Subgroup X} [Q.Normal] [IsSimpleGroup (X ⧸ Q)]
    {H : Subgroup X} (hH : H.Normal) (hQH : Q ≤ H) : H ≤ Q ∨ H = ⊤ := by
  have : (H.map (QuotientGroup.mk' Q)).Normal := hH.map _ (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.map (QuotientGroup.mk' Q)) with h | h
  · left
    intro x hx
    have hm : QuotientGroup.mk' Q x ∈ H.map (QuotientGroup.mk' Q) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff x).mp hm
  · right
    refine eq_top_of_forall_mk hQH fun x => ?_
    have hm : QuotientGroup.mk' Q x ∈ H.map (QuotientGroup.mk' Q) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hm
    exact ⟨y, hy, hyx⟩

omit [Finite X] in
theorem eq_top_of_closure_image {Q : Subgroup X} [Q.Normal] {H : Subgroup X} (hQH : Q ≤ H)
    {S : Set X} (hS : S ⊆ H) (hgen : Subgroup.closure (QuotientGroup.mk' Q '' S) = ⊤) :
    H = ⊤ := by
  refine eq_top_of_forall_mk hQH fun x => ?_
  have hle : Subgroup.closure (QuotientGroup.mk' Q '' S) ≤ H.map (QuotientGroup.mk' Q) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hS hs, rfl⟩
  rw [hgen] at hle
  obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_top (QuotientGroup.mk' Q x))
  exact ⟨y, hy, hyx⟩

theorem false_of_relIndex_center_le
    {Q V : Subgroup X} [hQ : Q.Normal] (e : X ⧸ Q ≃* NativeSporadic.J2) (hVn : V.Normal)
    (hV : IsElemTwo V) (hQV : Q ≤ Subgroup.centralizer (V : Set X))
    (hVZ : ¬ V ≤ Subgroup.center X) (hcard : (Subgroup.center X).relIndex V ≤ 2 ^ 8) : False := by
  have hsimple : IsSimpleGroup (X ⧸ Q) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have hVn' := hVn
  set N : Subgroup X := V ⊓ Subgroup.center X with hN
  have hNn : N.Normal := Subgroup.normal_inf_normal V (Subgroup.center X)
  set W : Subgroup (X ⧸ N) := V.map (QuotientGroup.mk' N) with hW
  have hWn : W.Normal := hVn.map _ (QuotientGroup.mk'_surjective N)
  have hWc : ∀ a b : W, a * b = b * a := by
    rintro ⟨_, v, hv, rfl⟩ ⟨_, w, hw, rfl⟩
    apply Subtype.ext
    change QuotientGroup.mk' N v * QuotientGroup.mk' N w =
      QuotientGroup.mk' N w * QuotientGroup.mk' N v
    rw [← map_mul, ← map_mul, hV.1 v hv w hw]
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hWc }
  have hW2 : ∀ w : W, w ^ 2 = 1 := by
    rintro ⟨_, v, hv, rfl⟩
    apply Subtype.ext
    change QuotientGroup.mk' N v ^ 2 = 1
    rw [← map_pow, pow_two, hV.2 v hv, map_one]
  have hWcard : Nat.card W ≤ 2 ^ 8 := by
    rw [hW, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hN, inf_comm,
      Subgroup.inf_relIndex_right]
    exact hcard
  set ρ₀ : X →* MulAut W := (MulAut.conjNormal (H := W)).comp (QuotientGroup.mk' N) with hρ₀
  have hρ₀v : ∀ (x v : X) (hv : v ∈ V),
      ((ρ₀ x ⟨QuotientGroup.mk' N v, v, hv, rfl⟩ : W) : X ⧸ N) =
        QuotientGroup.mk' N (x * v * x⁻¹) := by
    intro x v hv
    rw [hρ₀, MonoidHom.comp_apply, MulAut.conjNormal_apply]
    simp only [map_mul, map_inv]
  have hQρ : Q ≤ ρ₀.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun w => ?_
    obtain ⟨_, v, hv, rfl⟩ := w
    apply Subtype.ext
    rw [hρ₀v q v hv, MulAut.one_apply]
    have hqv : v * q = q * v := Subgroup.mem_centralizer_iff.mp (hQV hq) v hv
    rw [show q * v * q⁻¹ = v by rw [← hqv, mul_inv_cancel_right]]
  have hker : ρ₀.ker ≤ Q := by
    rcases le_or_eq_top_of_normal (MonoidHom.normal_ker ρ₀) hQρ with h | h
    · exact h
    exfalso
    have hsq : ∀ x : X, x * x ∈ Subgroup.centralizer (V : Set X) := by
      intro x
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hx : ρ₀ x = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top x
      have hc := congrArg (fun φ : MulAut W => ((φ ⟨QuotientGroup.mk' N v, v, hv, rfl⟩ : W) :
        X ⧸ N)) hx
      simp only [MulAut.one_apply] at hc
      rw [hρ₀v x v hv] at hc
      have hcN : (x * v * x⁻¹)⁻¹ * v ∈ N := QuotientGroup.eq.mp hc
      set c := (x * v * x⁻¹)⁻¹ * v with hcdef
      have hcV : c⁻¹ ∈ V := V.inv_mem hcN.1
      have hcZ : c⁻¹ ∈ Subgroup.center X := Subgroup.inv_mem _ hcN.2
      have hcc : c⁻¹ * c⁻¹ = 1 := hV.2 _ hcV
      have hxc : x * c⁻¹ * x⁻¹ = c⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hcZ x, mul_inv_cancel_right]
      have hy : x * v * x⁻¹ = v * c⁻¹ := by rw [hcdef]; group
      have key : x * x * v * (x * x)⁻¹ = v := by
        calc x * x * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
          _ = x * (v * c⁻¹) * x⁻¹ := by rw [hy]
          _ = (x * v * x⁻¹) * (x * c⁻¹ * x⁻¹) := by group
          _ = v * (c⁻¹ * c⁻¹) := by rw [hy, hxc]; group
          _ = v := by rw [hcc, mul_one]
      calc v * (x * x) = x * x * v * (x * x)⁻¹ * (x * x) := by rw [key]
        _ = x * x * v := by group
    rcases le_or_eq_top_of_normal (Subgroup.normal_centralizer (H := V)) hQV with hCQ | hCtop
    ·
      have hsq' : ∀ y : NativeSporadic.J2, y * y = 1 := by
        intro y
        obtain ⟨q, rfl⟩ := e.surjective y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q q
        have h1 : QuotientGroup.mk' Q (x * x) = 1 :=
          (QuotientGroup.eq_one_iff (x * x)).mpr (hCQ (hsq x))
        rw [← map_mul, ← map_mul, h1, map_one]
      obtain ⟨a, b, hab⟩ := CFSG.Sporadic.SmallOddCore.j2_not_comm
      apply hab
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq' a)
      have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq' b)
      have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq' (a * b))
      rw [← hab', mul_inv_rev, ha, hb]
    · apply hVZ
      intro v hv
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer (V : Set X) := by
        rw [hCtop]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg v hv).symm
  set ρ : X ⧸ Q →* MulAut W := QuotientGroup.lift Q ρ₀ hQρ with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q z
    rw [QuotientGroup.mk'_apply, hρ, QuotientGroup.lift_mk] at hz
    exact (QuotientGroup.eq_one_iff x).mpr (hker hz)
  set π : X ⧸ Q →* NativeSporadic.J2 := (e : X ⧸ Q →* NativeSporadic.J2) with hπ
  have hπx : ∀ z : X ⧸ Q, π z = e z := fun z => rfl
  refine CFSG.CGT.PushingUpLit.CGT6M.false_of_j2_image hW2 hWcard ρ hρinj π
    (fun y => ⟨e.symm y, by rw [hπx, MulEquiv.apply_symm_apply]⟩) ?_
  intro z hz
  have hz1 : z = 1 := e.injective (by rw [map_one, ← hπx]; exact hz)
  rw [hz1]
  exact Subgroup.one_mem _

theorem relIndex_centralizer_conj_le {V : Subgroup X} (hVn : V.Normal) (g t : X) :
    (Subgroup.centralizer ({g * t * g⁻¹} : Set X)).relIndex V ≤
      (Subgroup.centralizer ({t} : Set X)).relIndex V := by
  have hVn' := hVn
  set φ : X →* X := (MulAut.conj g : X →* X) with hφ
  have hinj : Function.Injective φ := (MulAut.conj g).injective
  have hVφ : V.map φ = V := Subgroup.Normal.map_conj_eq V g
  have hle : (Subgroup.centralizer ({t} : Set X)).map φ ≤
      Subgroup.centralizer ({g * t * g⁻¹} : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * z * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * z * g⁻¹)
    calc g * z * g⁻¹ * (g * t * g⁻¹) = g * (z * t) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hz]
      _ = g * t * g⁻¹ * (g * z * g⁻¹) := by group
  calc (Subgroup.centralizer ({g * t * g⁻¹} : Set X)).relIndex V
      ≤ ((Subgroup.centralizer ({t} : Set X)).map φ).relIndex V :=
        Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)
    _ = ((Subgroup.centralizer ({t} : Set X)).map φ).relIndex (V.map φ) := by rw [hVφ]
    _ = (Subgroup.centralizer ({t} : Set X)).relIndex V :=
        Subgroup.relIndex_map_map_of_injective _ _ hinj

theorem four_lt_relIndex_centralizer
    {Q V : Subgroup X} [Q.Normal]
    (e : X ⧸ Q ≃* NativeSporadic.J2) (hVn : V.Normal) (hV : IsElemTwo V)
    (hQV : Q ≤ Subgroup.centralizer (V : Set X)) (hVZ : ¬ V ≤ Subgroup.center X) {t : X}
    (htQ : t ∉ Q) (ht2 : t * t ∈ Q) :
    4 < (Subgroup.centralizer ({t} : Set X)).relIndex V := by
  by_contra hle
  rw [not_lt] at hle
  set π : X →* X ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hτ : orderOf (π t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two]
      exact (QuotientGroup.eq_one_iff (t * t)).mpr ht2
    · intro h1
      exact htQ ((QuotientGroup.eq_one_iff t).mp h1)
  obtain ⟨c₁, c₂, c₃, c₄, hgen⟩ := exists_four_conj_closure_eq_top_of_equiv e hτ
  obtain ⟨g₁, rfl⟩ := hπs c₁
  obtain ⟨g₂, rfl⟩ := hπs c₂
  obtain ⟨g₃, rfl⟩ := hπs c₃
  obtain ⟨g₄, rfl⟩ := hπs c₄
  set H : Subgroup X := Subgroup.centralizer ({g₁ * t * g₁⁻¹} : Set X) ⊓
    Subgroup.centralizer ({g₂ * t * g₂⁻¹} : Set X) ⊓
    Subgroup.centralizer ({g₃ * t * g₃⁻¹} : Set X) ⊓
    Subgroup.centralizer ({g₄ * t * g₄⁻¹} : Set X) with hH
  have hb : ∀ g : X, (Subgroup.centralizer ({g * t * g⁻¹} : Set X)).relIndex V ≤ 4 :=
    fun g => (relIndex_centralizer_conj_le hVn g t).trans hle
  have hHle : H.relIndex V ≤ 2 ^ 8 := by
    refine Subgroup.relIndex_inf_le.trans ?_
    refine (Nat.mul_le_mul_right _ Subgroup.relIndex_inf_le).trans ?_
    refine (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Subgroup.relIndex_inf_le)).trans ?_
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hb g₁) (hb g₂)) (hb g₃)) (hb g₄)
    exact this.trans (by norm_num)
  have hHZ : H ⊓ V ≤ Subgroup.center X ⊓ V := by
    rintro v ⟨hvH, hvV⟩
    refine ⟨?_, hvV⟩
    change v ∈ Subgroup.center X
    have hcomm : ∀ g : X, v ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set X) →
        g * t * g⁻¹ ∈ Subgroup.centralizer ({v} : Set X) := fun g hg => by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      exact hg.symm
    have hQv : Q ≤ Subgroup.centralizer ({v} : Set X) := fun q hq => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hQV hq) v hvV).symm
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hvH
    have himg : π '' ({g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹, g₃ * t * g₃⁻¹, g₄ * t * g₄⁻¹} : Set X) =
        {π g₁ * π t * (π g₁)⁻¹, π g₂ * π t * (π g₂)⁻¹, π g₃ * π t * (π g₃)⁻¹,
          π g₄ * π t * (π g₄)⁻¹} := by
      simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv]
    have htop := eq_top_of_closure_image hQv (S := {g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹,
        g₃ * t * g₃⁻¹, g₄ * t * g₄⁻¹}) (by
      rintro _ (rfl | rfl | rfl | rfl)
      · exact hcomm g₁ h₁
      · exact hcomm g₂ h₂
      · exact hcomm g₃ h₃
      · exact hcomm g₄ h₄) (by rw [← hπ, himg]; exact hgen)
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({v} : Set X) := by
      rw [htop]
      exact Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg
  refine false_of_relIndex_center_le e hVn hV hQV hVZ ?_
  calc (Subgroup.center X).relIndex V = (Subgroup.center X ⊓ V).relIndex V :=
        (Subgroup.inf_relIndex_right _ _).symm
    _ ≤ (H ⊓ V).relIndex V :=
        Subgroup.relIndex_le_of_le_left hHZ (relIndex_ne_zero_of_finite _ _)
    _ = H.relIndex V := Subgroup.inf_relIndex_right _ _
    _ ≤ 2 ^ 8 := hHle

end CFSG.RankThree.PartTwo.Sec15.Item322Scope
