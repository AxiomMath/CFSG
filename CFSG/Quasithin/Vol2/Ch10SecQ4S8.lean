module

public import CFSG.Quasithin.Vol2.Ch10SecBXi
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Vol2.Ch10SecEA5
public import CFSG.Quasithin.Vol2.Ch10SecEIdent

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Generic

variable {X : Type*} [Group X]

theorem conj_mem_oTwoUpper {K : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) {x : X} (hx : x ∈ oTwoUpper K) :
    g * x * g⁻¹ ∈ oTwoUpper K := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hy.1, ?_⟩
    have h := MulEquiv.orderOf_eq (MulAut.conj g) y
    rw [MulAut.conj_apply] at h
    rw [h]
    exact hy.2
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact (oTwoUpper K).mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact (oTwoUpper K).inv_mem ha

theorem le_normalizer_oTwoUpper (K : Subgroup X) :
    Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (oTwoUpper K : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_oTwoUpper hg, fun h => ?_⟩
  have := conj_mem_oTwoUpper (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this

end Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autI_le_normalizer {V A B : Subgroup G} (hel : IsElemAbelian 2 V)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    autI hel A ≤ Subgroup.normalizer (autI hel B : Set (MulAut (IntMod V hel))) := by
  have key : ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ A →
      ∀ ψ ∈ autI hel B, convI hel g * ψ * (convI hel g)⁻¹ ∈ autI hel B := by
    intro g hgA ψ hψ
    obtain ⟨h, hhB, rfl⟩ := (mem_autI hel).1 hψ
    rw [← map_inv, ← map_mul, ← map_mul]
    refine convI_mem_autI hel ?_ _
    exact (Subgroup.mem_normalizer_iff.mp (hAB hgA) h).mp hhB
  intro φ hφ
  obtain ⟨g, hgA, rfl⟩ := (mem_autI hel).1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  refine ⟨key g hgA ψ, fun h => ?_⟩
  have := key g⁻¹ (A.inv_mem hgA) _ h
  rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at this

theorem exists_noncomm_of_isA5Module {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)}
    (h : E2.IsA5Module K) : ∃ a ∈ oTwoUpper K, ∃ b ∈ oTwoUpper K, a * b ≠ b * a := by
  obtain ⟨θ, -, -⟩ := h
  have hodd : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 →
      ((θ.symm σ : ↥K) : MulAut W) ∈ oTwoUpper K := by
    intro σ h3 h1
    refine mem_oTwoUpper_of_odd (θ.symm σ).2 ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq θ.symm]
    exact SecE.odd_orderOf_of_pow_three h3 h1
  refine ⟨_, hodd _ SecE.cThree_pow_three SecE.cThree_ne_one, _,
    hodd _ SecE.cThree'_pow_three SecE.cThree'_ne_one, fun hab => ?_⟩
  have h1 : θ.symm SecE.cThree * θ.symm SecE.cThree' =
      θ.symm SecE.cThree' * θ.symm SecE.cThree := Subtype.ext hab
  rw [← map_mul, ← map_mul] at h1
  have h2 := θ.symm.injective h1
  revert h2
  decide +kernel

theorem exists_le_autI_map {V H T K : Subgroup G} (hel : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT2 : IsPGroup 2 T) (hK : K ∈ cComp H)
    (hKT : H = K ⊔ T) (h2J : oTwoUpper H ≤ thompsonJ H)
    {I' : Finset (Subgroup (MulAut (IntMod V hel)))}
    (hJ : autI hel (thompsonJ H) = ⨆ L ∈ I', L)
    (hcomm : ∀ L ∈ I', ∀ L' ∈ I', L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {K₀ : Subgroup (MulAut (IntMod V hel))} (hK₀ : K₀ ∈ I') (hA5 : E2.IsA5Module K₀) :
    ∃ t ∈ T, oTwoUpper K₀ ≤ autI hel (K.map (MulAut.conj t).toMonoidHom) := by
  set C := oTwoUpper K₀ with hC
  have hCs := SecE.isSimpleGroup_oTwoUpper_of_isA5Module hA5
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hJN : autI hel (thompsonJ H) ≤ Subgroup.normalizer (C : Set _) := by
    rw [hJ]
    refine iSup₂_le fun L hL => ?_
    refine le_trans ?_ (le_normalizer_oTwoUpper K₀)
    by_cases h : L = K₀
    · rw [h]; exact Subgroup.le_normalizer
    · exact SecE.le_normalizer_of_commute fun a ha b hb => hcomm L hL K₀ hK₀ h a ha b hb
  have hCO : C ≤ autI hel (oTwoUpper H) := by
    have hJH : thompsonJ H ≤ Subgroup.normalizer (V : Set G) := (thompsonJ_le_self H).trans hHN
    calc C ≤ oTwoUpper (autI hel (thompsonJ H)) :=
          oTwoUpper_mono (hJ ▸ le_iSup₂_of_le (f := fun L (_ : L ∈ I') => L) K₀ hK₀ le_rfl)
      _ = autI hel (oTwoUpper (thompsonJ H)) := SecE.oTwoUpper_autI hel hJH
      _ ≤ autI hel (oTwoUpper H) := autI_mono hel (oTwoUpper_mono (thompsonJ_le_self H))
  set N := conjClosure K T with hN
  have hNT : T ≤ Subgroup.normalizer (N : Set G) := le_normalizer_conjClosure K T
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hNH : N ≤ H := conjClosure_le fun t ht k hk =>
    H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
  have hHeq : H = N ⊔ T :=
    le_antisymm (hKT ▸ sup_le_sup_right (le_conjClosure K T) T) (sup_le hNH hTH)
  have hOH : oTwoUpper H ≤ N := by
    rw [hHeq, SecB.oTwoUpper_sup_eq hT2 hNT]
    exact oTwoUpper_le N
  have hKs : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ∈ cComp H := fun t ht =>
    H13.LocDbl.map_conj_mem_cComp hK (Subgroup.le_normalizer (hTH ht))
  by_contra hno
  push Not at hno
  have hcent : ∀ t ∈ T, ∀ a ∈ C, ∀ b ∈ autI hel (K.map (MulAut.conj t).toMonoidHom),
      a * b = b * a := by
    intro t ht
    have hKtN : N ≤ Subgroup.normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G) := conjClosure_le fun s hs k hk =>
      le_normalizer_of_mem_cComp (hKs t ht) (hKs s hs) ⟨k, hk, rfl⟩
    have hCN : C ≤ Subgroup.normalizer (autI hel (K.map (MulAut.conj t).toMonoidHom) : Set _) :=
      hCO.trans ((autI_mono hel hOH).trans (autI_le_normalizer hel hKtN))
    have hKtJ : K.map (MulAut.conj t).toMonoidHom ≤ thompsonJ H := by
      have h1 := oTwoUpper_mono (le_of_mem_cComp (hKs t ht))
      rw [← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp (hKs t ht))] at h1
      exact h1.trans h2J
    have hi := (SecE.inf_eq_bot_or_le hCs hCN).resolve_right (hno t ht)
    exact SecE.commute_of_inf_eq_bot hi hCN ((autI_mono hel hKtJ).trans hJN)
  have hNP : N ≤ preI hel H hHN (Subgroup.centralizer (C : Set _)) := by
    refine conjClosure_le fun t ht k hk => ?_
    have hx : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
    have hxH : t * k * t⁻¹ ∈ H := le_of_mem_cComp (hKs t ht) hx
    refine (mem_preI hel).2 ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    rw [convHom_apply]
    exact hcent t ht a ha _ (convI_mem_autI hel hx _)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isA5Module hA5
  apply hab
  have hbP : b ∈ autI hel (preI hel H hHN (Subgroup.centralizer (C : Set _))) :=
    autI_mono hel (hOH.trans hNP) (hCO hb)
  obtain ⟨g, hgP, rfl⟩ := (mem_autI hel).1 hbP
  obtain ⟨hgH, hgc⟩ := (mem_preI hel).1 hgP
  rw [convHom_apply] at hgc
  exact Subgroup.mem_centralizer_iff.mp hgc a ha

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
