module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB14

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem Oo_comm (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∀ a ∈ OoOf δ, ∀ b ∈ OoOf δ, a * b = b * a := by
  obtain ⟨c, V₀, -, -, -, -, -, -, -, -, -, hel, -⟩ := h.A3 hA
  exact fun a ha b hb => isElemAbelian_comm hel ha hb

theorem relIndex_Oo_eq_aZ (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hij : j ≠ i) :
    (OoOf i ⊓ Qv j).relIndex (OoOf i) = aZ i j := by
  obtain ⟨U', hi'⟩ := h.exists_at hi
  exact (hi'.relIndex_Zv_eq_Oo hA hj hij).symm

theorem false_of_a2 (hA : F53Amalgam H M S) (h : ConfR δ μ U)
    (h2 : ∃ n ∈ nbrs μ, n ≠ δ ∧ aZ δ n = 2) : False := by
  obtain ⟨n₀, hn₀, hn₀δ, ha⟩ := h2
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have ha2 : ∀ i j : Geo H M, i ∈ nbrs μ → j ∈ nbrs μ → i ≠ j → aZ i j = 2 := fun i j hi hj hij =>
    (h.aZ_unif hA hi hj hδ hn₀ hij (Ne.symm hn₀δ)).trans ha
  obtain ⟨n, n', hn, hn', hnδ, hn'δ, hnn', hall⟩ := nbrs_three hA (h.vtype_mu hA) hδ
  obtain ⟨Un, hcn⟩ := h.exists_at hn
  obtain ⟨Un', hcn'⟩ := h.exists_at hn'
  have hallN : ∀ x ∈ nbrs μ, x = n ∨ x = δ ∨ x = n' := fun x hx => by
    rcases hall x hx with e | e | e <;> simp [e]
  have hallN' : ∀ x ∈ nbrs μ, x = n' ∨ x = δ ∨ x = n := fun x hx => by
    rcases hall x hx with e | e | e <;> simp [e]
  have hXX := hcn.inf_Qv_ne hA hδ hn' (Ne.symm hnδ) (Ne.symm hnn') (Ne.symm hn'δ) hallN
    (ha2 n δ hn hδ hnδ)
  have hYY := hcn'.inf_Qv_ne hA hδ hn (Ne.symm hn'δ) hnn' (Ne.symm hnδ) hallN'
    (ha2 n' δ hn' hδ hn'δ)
  have hXi : (OoOf n ⊓ Qv δ).relIndex (OoOf n) = 2 := by
    rw [hcn.relIndex_Oo_eq_aZ hA hn hδ (Ne.symm hnδ)]; exact ha2 n δ hn hδ hnδ
  have hX'i : (OoOf n ⊓ Qv n').relIndex (OoOf n) = 2 := by
    rw [hcn.relIndex_Oo_eq_aZ hA hn hn' (Ne.symm hnn')]; exact ha2 n n' hn hn' hnn'
  have hYi : (OoOf n' ⊓ Qv δ).relIndex (OoOf n') = 2 := by
    rw [hcn'.relIndex_Oo_eq_aZ hA hn' hδ (Ne.symm hn'δ)]; exact ha2 n' δ hn' hδ hn'δ
  have hY'i : (OoOf n' ⊓ Qv n).relIndex (OoOf n') = 2 := by
    rw [hcn'.relIndex_Oo_eq_aZ hA hn' hn hnn']; exact ha2 n' n hn' hn (Ne.symm hnn')
  have hX'B : ∀ x ∈ OoOf n ⊓ Qv n', ∀ b ∈ OoOf n', x * b = b * x := by
    intro x hx b hb
    rw [h.Oo_inf_Qv_eq hA hn hn'] at hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 b hb).symm
  have hY'A : ∀ y ∈ OoOf n' ⊓ Qv n, ∀ a ∈ OoOf n, y * a = a * y := by
    intro y hy a ha
    rw [h.Oo_inf_Qv_eq hA hn' hn] at hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 a ha).symm
  obtain ⟨s, hs, hsP, -, hX⟩ := h.lemmaX hA
  have hsG : (s : G) ∈ stab μ := hs.2
  set sE : ↥(H ⊔ M) := toGeoElt μ hsG with hsE
  have hsswap : sE • n = n' :=
    h.swap_of_not_Qv hA hn hn' hnδ hn'δ hnn' hall (s := sE) hs.1 hsG hsP
  have hsδ : sE • δ = δ := smul_eq_of_mem_stab (g := sE) hs.1
  have hYX : OoOf n' ⊓ Qv δ = conjSub s (OoOf n ⊓ Qv δ) := by
    have e1 := OoOf_smul sE n
    have e2 := Qv_smul sE δ
    rw [hsswap] at e1
    rw [hsδ] at e2
    rw [conjSub_inf]
    exact congrArg₂ (· ⊓ ·) e1 e2
  have hXY : ∀ x ∈ OoOf n ⊓ Qv δ, ∀ y ∈ OoOf n' ⊓ Qv δ, x * y = y * x := by
    intro x hx y hy
    rw [hYX] at hy
    have hb : s⁻¹ * y * s ∈ OoOf n ⊓ Qv δ := mem_conjSub.mp hy
    have := hX (OoOf n ⊓ Qv δ) inf_le_right
      (fun a ha b hb' => hcn.Oo_comm hA a ha.1 b hb'.1) x hx _ hb
    have e : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rwa [e] at this
  have hne : OoOf n ⊓ Qv n' ≠ OoOf n := fun e => by
    have := Subgroup.relIndex_eq_one.mpr (le_of_eq e.symm)
    rw [this] at hX'i; omega
  obtain ⟨a, haO, haX⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne inf_le_left hne)
  have hac : a ∉ Subgroup.centralizer (OoOf n' : Set G) := by
    intro hc
    apply haX
    rw [hcn.Oo_inf_Qv_eq hA hn hn']
    exact ⟨haO, hc⟩
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ OoOf n', b * a ≠ a * b := by
    by_contra hcon
    push Not at hcon
    exact hac (Subgroup.mem_centralizer_iff.mpr hcon)
  exact hba (commute_of_index_two (hcn.Oo_comm hA) (hcn'.Oo_comm hA) inf_le_left inf_le_left
    inf_le_left inf_le_left hXi hX'i hYi hY'i hXX hYY hX'B hY'A hXY a haO b hb).symm

end ConfR

end CFSG.Quasithin.F53
