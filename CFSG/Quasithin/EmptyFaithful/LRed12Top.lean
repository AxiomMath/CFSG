module

public import CFSG.Quasithin.EmptyFaithful.LRed12Hyp
public import CFSG.Quasithin.EmptyFaithful.LRed12J
public import CFSG.Quasithin.EmptyFaithful.LRed12Cen
public import CFSG.Quasithin.EmptyFaithful.LRed12ASemi
public import CFSG.Quasithin.EmptyFaithful.LRed12BGrp
public import CFSG.Quasithin.Background.D2Z3
public import CFSG.Quasithin.EmptyFaithful.Gap6R0Stmt
public import CFSG.Quasithin.EmptyFaithful.S151cGlue

public section

namespace CFSG.Quasithin

namespace LRed12

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.Gap6
open scoped commutatorElement

section Helpers

variable {V : Type*} [CommGroup V]

theorem commSub_conj_mem {W : Subgroup V} {Y : Subgroup (MulAut V)} {g : MulAut V}
    (hgW : ∀ w ∈ W, g w ∈ W) (hgY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    ∀ w ∈ commSub W Y, g w ∈ commSub W Y := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w', hw', rfl⟩ := hc
    have h1 : g (x w' * w'⁻¹) = (g * x * g⁻¹) (g w') * (g w')⁻¹ := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨_, hgY x hx, g w', hgW w' hw', rfl⟩
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem zpowers_conj_mem {g z : MulAut V} (h : g * z * g⁻¹ ∈ Subgroup.zpowers z) :
    ∀ y ∈ Subgroup.zpowers z, g * y * g⁻¹ ∈ Subgroup.zpowers z := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have : g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [this]
  exact Subgroup.zpow_mem _ h k

end Helpers

section Main

variable {V : Type*} [CommGroup V] [Finite V] {X Tb : Subgroup (MulAut V)}

theorem no_excShape (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) (hsqtk : IsQuotientOfSQTKTC ↥X) (hsyl : Tb ∈ sylow2Of X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) : ¬ ExcShape X A := by
  classical
  rintro ⟨hrk, -, hμ, hk⟩
  set F : Subgroup (MulAut V) := fittingOf (Jhat X) with hFdef
  have hJX : Jhat X ≤ X := Jhat_le X
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hAel := hA2.isElemAbelian2
  have hAX : A ≤ X := hA2.le
  have hAJ : A ≤ Jhat X := fun a ha => le_Jhat hA ha
  have hrk1 : 1 < rk A := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, e, hbA, heA, hb1, he1, hbe, hb2, he2, hbeC, hmem, hy, hrb, hre, hbC⟩ :=
    exc_config hV hsolv hO2 hA hrk hμ hk
  have hbJ : b ∈ Jhat X := hAJ hbA
  obtain ⟨g, hgX, j, hjcl, hbj, ⟨n, hjn⟩, hjC⟩ :=
    exists_three_element hV hsolv hO2 hsyl hgen hbJ hb2 hbC
  have hb'J : g * b * g⁻¹ ∈ Jhat X := conj_mem_Jhat hgX hbJ
  have hjJ : j ∈ Jhat X := by
    have : Subgroup.closure ({b, g * b * g⁻¹} : Set (MulAut V)) ≤ Jhat X := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hbJ
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hb'J
    exact this hjcl
  have hA' : conjBy g A ∈ QhatStar X := conjBy_mem_QhatStar hA hgX
  have hrk' : 1 < rk (conjBy g A) := by
    have : rk (conjBy g A) = rk A := by
      unfold rk
      rw [card_conjBy]
    omega
  have hj5 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ y ∈ pCoreOf p X, j * y = y * j := by
    intro p hp hp2 hp3 y hy
    have h1 := centralizes_pCore_of_qhatStar hV hA hrk1 hp hp2 hp3
    have h2 := centralizes_pCore_of_qhatStar hV hA' hrk' hp hp2 hp3
    have hcl : Subgroup.closure ({b, g * b * g⁻¹} : Set (MulAut V)) ≤
        Subgroup.centralizer (pCoreOf p X : Set (MulAut V)) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact h1 hbA
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact h2 (mem_conjBy_of_mem hbA)
    exact (Subgroup.mem_centralizer_iff.mp (hcl hjcl) y hy).symm
  obtain ⟨y₀, hy₀, hjy₀⟩ := not_centralizes_pCore_three hsolv hO2 hjJ hj5 hjC
  set PJ : Subgroup (MulAut V) := pCoreOf 3 (Jhat X) with hPJ
  have hPJ3 : IsPGroup 3 PJ := pCoreOf_isPGroup 3 (Jhat X)
  have hjPJ : ∀ y ∈ PJ, j * y * j⁻¹ ∈ PJ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 (Jhat X) hjJ) y).mp hy
  have hbPJ : ∀ y ∈ PJ, b * y * b⁻¹ ∈ PJ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_Jhat 3 (hAX hbA)) y).mp hy
  set Λ : Subgroup (MulAut V) := PJ ⊔ Subgroup.zpowers j with hΛ
  have hΛ3 : IsPGroup 3 Λ := isPGroup_three_sup_zpowers hPJ3 ⟨n, hjn⟩ hjPJ
  have hjΛ : j ∈ Λ := Subgroup.mem_sup_right (Subgroup.mem_zpowers j)
  have hbΛ : ∀ y ∈ Λ, b * y * b⁻¹ ∈ Λ := by
    have hle : Λ ≤ Λ.comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact (le_sup_left : PJ ≤ Λ) (hbPJ y hy)
      · show b * j * b⁻¹ ∈ Λ
        rw [hbj]
        exact Λ.inv_mem hjΛ
    intro y hy
    exact hle hy
  have hnc : ∃ x ∈ Λ, ∃ y ∈ Λ, x * y ≠ y * x :=
    ⟨y₀, (le_sup_left : PJ ≤ Λ) hy₀, j, hjΛ, fun h => hjy₀ h.symm⟩
  obtain ⟨z, hzΛ, hzcomm, hz1, hz3, hzcent, hzeig⟩ := exists_central_comm_eigen hΛ3 hb2 hbΛ hnc
  have hzPJ : z ∈ PJ :=
    (Subgroup.commutator_le.mpr (commutator_mem_of_sup_zpowers hjPJ)) hzcomm
  have hzJ : z ∈ Jhat X := pCoreOf_le 3 (Jhat X) hzPJ
  have hzX : z ∈ X := hJX hzJ
  have hu : ∃ u : MulAut V, u ∈ X ∧ u ^ 2 = 1 ∧ u * z * u⁻¹ = z⁻¹ ∧
      rk ↥(commSub (commV F) (Subgroup.zpowers u)) ≤ 2 := by
    rcases hzeig with h | h
    ·
      have hPp : IsPGroup 3 (pCoreOf 3 X) := pCoreOf_isPGroup 3 X
      have hAn : ∀ a ∈ A, ∀ y ∈ pCoreOf 3 X, a * y * a⁻¹ ∈ pCoreOf 3 X := fun a ha y hy =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (hAX ha)) y).mp hy
      have hfaith3 := faithful_pCore_three_of_qhatStar hV hsolv hO2 hA hrk1
      have hcyc := isCyclic_inf_centralizer_of_faithful (X := X) (P := pCoreOf 3 X) (A := A)
        (p := 3) (by norm_num) (pCoreOf_le 3 X) hPp hAel hAX hAn hsqtk hfaith3 hbA hb1
      set Y : Subgroup (MulAut V) :=
        pCoreOf 3 X ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) with hY
      have : IsCyclic ↥Y := hcyc
      have hY3 : IsPGroup 3 Y := hPp.to_le inf_le_left
      have hzY : z ∈ Y := by
        refine ⟨pCoreOf_Jhat_le 3 hzPJ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have : b * z * b⁻¹ = z := h
        calc z * b = (b * z * b⁻¹) * b := by rw [this]
          _ = b * z := by group
      have hbe_inv : b * e⁻¹ = e⁻¹ * b := (show Commute b e from hbeC).inv_right.eq
      have hσY : ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := by
        intro y hy
        refine ⟨hAn e heA y hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
        calc (e * y * e⁻¹) * b = e * y * (e⁻¹ * b) := by group
          _ = e * y * (b * e⁻¹) := by rw [hbe_inv]
          _ = e * (y * b) * e⁻¹ := by group
          _ = e * (b * y) * e⁻¹ := by rw [hyb]
          _ = (e * b) * y * e⁻¹ := by group
          _ = (b * e) * y * e⁻¹ := by rw [hbeC]
          _ = b * (e * y * e⁻¹) := by group
      have hnt : ∃ y ∈ Y, e * y ≠ y * e := by
        obtain ⟨y, hyY, a, haA, hne⟩ := hy
        have hyb' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hyY.2
        have hyb : b * y = y * b := hyb'.symm
        refine ⟨y, hyY, fun hey => ?_⟩
        rcases hmem a haA with rfl | rfl | rfl | rfl
        · exact hne (by simp)
        · exact hne hyb
        · exact hne hey
        · apply hne
          calc b * e * y = b * (e * y) := by group
            _ = b * (y * e) := by rw [hey]
            _ = (b * y) * e := by group
            _ = (y * b) * e := by rw [hyb]
            _ = y * (b * e) := by group
      have hinv := inv_of_involution_of_cyclic hY3 he2 hσY hnt z hzY
      exact ⟨e, hAX heA, he2, hinv, hre⟩
    · exact ⟨b, hAX hbA, hb2, h, hrb⟩
  obtain ⟨u, huX, hu2, huz, hru⟩ := hu
  have hV₀ : ∀ g ∈ X, ∀ v ∈ commV F, g v ∈ commV F := fun g hg v hv => apply_mem_commV_F hg hv
  have hzpX : ∀ x ∈ Subgroup.zpowers z, x ∈ X := fun x hx => (Subgroup.zpowers_le.mpr hzX) hx
  have hΛX : Λ ≤ X :=
    sup_le ((pCoreOf_le 3 (Jhat X)).trans hJX) (Subgroup.zpowers_le.mpr (hJX hjJ))
  set U : Subgroup V := commSub (commV F) (Subgroup.zpowers z) with hU
  have hUV₀ : U ≤ commV F := commSub_le_of_invariant fun x hx w hw => hV₀ x (hzpX x hx) w hw
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hUz : ∀ w ∈ U, z w ∈ U := by
    intro w hw
    have h1 : z w * w⁻¹ ∈ U :=
      Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, w, hUV₀ hw, rfl⟩
    have : z w = (z w * w⁻¹) * w := by group
    rw [this]
    exact U.mul_mem h1 hw
  have hzu : u * z * u⁻¹ ∈ Subgroup.zpowers z := by
    rw [huz]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)
  have hUu : ∀ w ∈ U, u w ∈ U :=
    commSub_conj_mem (fun w hw => hV₀ u huX w hw) (zpowers_conj_mem hzu)
  have hUΛ : ∀ g' ∈ Λ, ∀ w ∈ U, g' w ∈ U := by
    intro g' hg' w hw
    have hgz : g' * z * g'⁻¹ ∈ Subgroup.zpowers z := by
      rw [show g' * z * g'⁻¹ = z by rw [hzcent g' hg']; group]
      exact Subgroup.mem_zpowers z
    exact commSub_conj_mem (fun w hw => hV₀ g' (hΛX hg') w hw) (zpowers_conj_mem hgz) w hw
  have hfpf : ∀ w ∈ U, z w = w → w = 1 := by
    intro w hw hzw
    have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
      rw [Nat.card_zpowers, hzord]; exact ⟨1, rfl⟩
    have h2 := (coprime_decomp hodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top w)).2
    have hw' : w ∈ commSub ⊤ (Subgroup.zpowers z) ⊓ (⊤ ⊓ fixV (Subgroup.zpowers z)) :=
      ⟨commSub_mono le_top le_rfl hw, Subgroup.mem_top w, mem_fixV_zpowers_iff.mpr hzw⟩
    rw [h2, Subgroup.mem_bot] at hw'
    exact hw'
  have hU4 : rk U ≤ 4 := by
    have := rk_le_two_mul_rk_commSub_of_inverts hV hz3 hu2 huz hUV₀ hUu hUz hfpf
    omega
  have hcomm : ⁅Λ, Λ⁆ ≤ centSub U := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact comm_mem_centSub_of_small hV hU4 hΛ3 hUΛ hg₁ hg₂
  have hzU : ∀ w ∈ U, z w = w := mem_centSub.mp (hcomm hzcomm)
  have hUbot : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun w hw => hfpf w hw (hzU w hw)
  have hfix : commV F ≤ fixV (Subgroup.zpowers z) := commSub_eq_bot_iff.mp hUbot
  exact hz1 (eq_one_of_fix_commV hV hsolv hO2 hzJ fun v hv =>
    mem_fixV_zpowers_iff.mp (hfix hv))

end Main

section Ambient

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem row24Residual_of_stage1416 (h1416 : StageLemma1416) : Row24Residual := by
  intro G _ _ T Mc M h hM hVe A hA
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have := h.simple
  exact no_excShape (IntMod.sq_eq_one) (isSolvable_autI_VZ h1416 h hM hVe)
    (pCoreOf_autI_VZ h hM hVe)
    (isQuotientOfSQTK_autI h.qtke h.nonabelian hM.1.1.1 hVe hMN)
    (autI_mem_sylow2Of h hM.1.1 hVe hMN) (gen_autI_VZ h hM.1.1 hVe) hA

end Ambient

end LRed12

end CFSG.Quasithin
