module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNineDepDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprimBase
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprimMon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeDep_noImprim {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x)
    (two : 2 ≤ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)))
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) (hρ : GGLargeRestr r s hA) :
    ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV (ggLargeRho r s hA).range := by
  classical
  intro himp
  let Tsub : Submodule (ZMod p) V := ggFixLineT r s
  let P : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r)
  let Q : Subgroup (↥Tsub ≃ₗ[ZMod p] ↥Tsub) := (ggLargeRho r s hA).range
  let d : ℕ := Module.finrank (ZMod p) ↥Tsub
  let φ : Equiv.Perm (Fin (N - 1 + 1)) →* (V ≃ₗ[ZMod p] V) := l04fD4_phiCox L
  have : Finite T := L.finT
  have : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s L.s_refl L.fix_s
  have : Module.Finite (ZMod p) ↥Tsub := inferInstance
  obtain ⟨b, hmon⟩ := ggRC_monomial_of_imprimitive (p := p) (V := ↥Tsub) (n := d) rfl
    Q hρ.2.1 hρ.2.2 himp
  obtain ⟨π, hπ, hπker, hπcomm, hπp⟩ := ggRC_monomial_hom b Q hmon
  have hker_bot : φ.ker = ⊥ := by
    by_contra hne
    have : φ.ker.Normal := MonoidHom.normal_ker _
    have hnt : Nontrivial ↥(φ.ker) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hAle : alternatingGroup (Fin (N - 1 + 1)) ≤ φ.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin (N - 1 + 1))
        (by rw [Nat.card_fin]; have := L.N_ge; omega) hnt
    let k0 : Fin (N - 1) := ⟨0, by have := L.N_ge; omega⟩
    let k1 : Fin (N - 1) := ⟨1, by have := L.N_ge; omega⟩
    have hne0 : k0.castSucc ≠ k0.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    have hne1 : k1.castSucc ≠ k1.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    have hprod_mem : Equiv.swap k0.castSucc k0.succ * Equiv.swap k1.castSucc k1.succ ∈
        alternatingGroup (Fin (N - 1 + 1)) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap hne0, Equiv.Perm.sign_swap hne1]
      norm_num
    have hval : φ (Equiv.swap k0.castSucc k0.succ * Equiv.swap k1.castSucc k1.succ) = 1 :=
      hAle hprod_mem
    rw [map_mul, l04fD4_phiCox_swap L k0, l04fD4_phiCox_swap L k1] at hval
    exact l04fD4_adjacent_ne_one L (by simp [k0, k1])
      (by have := L.N_ge; simp only [k1]; omega) hval
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff _).mp hker_bot
  have hGen : Subgroup.closure (Set.range (fun k : Fin (N - 1) => Equiv.swap k.castSucc k.succ)) = ⊤ := by
    apply le_antisymm le_top
    intro π _
    have hm : π ∈ Submonoid.closure
        (Set.range (fun k : Fin (N - 1) => Equiv.swap k.castSucc k.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact trivial
    have hle : Submonoid.closure (Set.range (fun k : Fin (N - 1) => Equiv.swap k.castSucc k.succ))
        ≤ (Subgroup.closure (Set.range (fun k : Fin (N - 1) => Equiv.swap k.castSucc k.succ))).toSubmonoid :=
      Submonoid.closure_le.mpr (fun x hx => Subgroup.subset_closure hx)
    exact hle hm
  have hphi_range : φ.range = P := by
    apply le_antisymm
    · rw [← Subgroup.map_top φ, ← hGen,
        MonoidHom.map_closure φ (Set.range (fun k : Fin (N - 1) => Equiv.swap k.castSucc k.succ))]
      apply Subgroup.closure_mono
      rintro x ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (l04fD4_phiCox_swap L k).symm⟩
    · rw [Subgroup.closure_le]
      rintro x ⟨k, rfl⟩
      exact ⟨Equiv.swap k.castSucc k.succ, l04fD4_phiCox_swap L k⟩
  let φP : Equiv.Perm (Fin (N - 1 + 1)) →* ↥P := φ.codRestrict P (fun x => by
    rw [← hphi_range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hφPinj : Function.Injective φP := by
    intro a b hab
    apply hinj
    exact congrArg (fun z : ↥P => (z : V ≃ₗ[ZMod p] V)) hab
  have hφPsurj : Function.Surjective φP := by
    intro q
    have hp : (q : V ≃ₗ[ZMod p] V) ∈ φ.range := by rw [hphi_range]; exact q.2
    obtain ⟨x, hx⟩ := hp
    exact ⟨x, Subtype.ext hx⟩
  let eP : Equiv.Perm (Fin (N - 1 + 1)) ≃* ↥P := MulEquiv.ofBijective φP ⟨hφPinj, hφPsurj⟩
  let hPA : P ≤ ggLargeGrp r s := Subgroup.closure_mono (Set.subset_union_left)
  let η : ↥P →* ↥Q :=
    ((ggLargeRho r s hA).codRestrict Q (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)).comp
      (Subgroup.inclusion hPA)
  let ψ : ↥P →* Equiv.Perm (Fin d) := π.comp η
  have hηinj : Function.Injective η := by
    intro a b hab
    have h1 : Subgroup.inclusion hPA a = Subgroup.inclusion hPA b :=
      hρ.1 (congrArg (fun q : ↥Q => (q : ↥Tsub ≃ₗ[ZMod p] ↥Tsub)) hab)
    exact Subtype.ext (congrArg (fun z : ↥(ggLargeGrp r s) => (z : V ≃ₗ[ZMod p] V)) h1)
  have hψcomm : IsMulCommutative (ψ.comp eP.toMonoidHom).ker := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    apply hφPinj
    show φP ((a : Equiv.Perm (Fin (N - 1 + 1))) * (b : Equiv.Perm (Fin (N - 1 + 1)))) =
      φP ((b : Equiv.Perm (Fin (N - 1 + 1))) * (a : Equiv.Perm (Fin (N - 1 + 1))))
    rw [map_mul, map_mul]
    apply hηinj
    rw [map_mul, map_mul]
    have ha : φP (a : (ψ.comp eP.toMonoidHom).ker) ∈ ψ.ker := a.2
    have hb : φP (b : (ψ.comp eP.toMonoidHom).ker) ∈ ψ.ker := b.2
    have hc := isMulCommutative_iff.mp hπcomm
      ⟨η (φP (a : (ψ.comp eP.toMonoidHom).ker) : ↥P), ha⟩
      ⟨η (φP (b : (ψ.comp eP.toMonoidHom).ker) : ↥P), hb⟩
    exact congrArg Subtype.val hc
  have hdle : d ≤ N := (Submodule.finrank_le Tsub).trans L.dim_le
  have hdge : N ≤ d := by
    by_contra hlt
    have hlt' : d < N - 1 + 1 := by
      have hN1 : N - 1 + 1 = N := by have := L.N_ge; omega
      rw [hN1]
      exact Nat.lt_of_not_le hlt
    exact ggRC_perm_not_monomial (N := N - 1 + 1) (m := d)
      (by have := L.N_ge; omega) hlt' (ψ.comp eP.toMonoidHom) hψcomm
  have hdN : d = N := le_antisymm hdle hdge
  have hfinT : Module.finrank (ZMod p) ↥Tsub = N := hdN
  have hTtop : Tsub = ⊤ := by
    have hVN : Module.finrank (ZMod p) V = N := by
      have h1 : d ≤ Module.finrank (ZMod p) V := Submodule.finrank_le Tsub
      have h2 : Module.finrank (ZMod p) V ≤ N := L.dim_le
      have h3 : d = N := hdN
      omega
    apply Submodule.eq_top_of_finrank_eq
    rw [hfinT, hVN]
  have hψker_comm : IsMulCommutative ψ.ker := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    apply hηinj
    show η (a.1 * b.1) = η (b.1 * a.1)
    rw [map_mul, map_mul]
    have ha : η a.1 ∈ π.ker := a.2
    have hb : η b.1 ∈ π.ker := b.2
    have hc := isMulCommutative_iff.mp hπcomm
      ⟨η a.1, ha⟩ ⟨η b.1, hb⟩
    exact congrArg Subtype.val hc
  have hψker_bot : ψ.ker = ⊥ := by
    let K : Subgroup (Equiv.Perm (Fin (N - 1 + 1))) := ψ.ker.map eP.symm.toMonoidHom
    have : K.Normal := Subgroup.Normal.map (MonoidHom.normal_ker ψ)
      eP.symm.toMonoidHom eP.symm.surjective
    have hKbot : K = ⊥ := by
      apply l04fD4_perm_normal_abelian_bot (N := N - 1 + 1)
        (by have := L.N_ge; omega) K
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (isMulCommutative_iff.mp hψker_comm ⟨x, hx⟩ ⟨y, hy⟩)
    apply le_antisymm _ bot_le
    intro x hx
    have hxK : eP.symm x ∈ K := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hKbot, Subgroup.mem_bot] at hxK
    have hx1 : x = 1 := by
      have := congrArg eP hxK
      simpa using this
    exact Subgroup.mem_bot.mpr hx1
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hψker_bot
  let giP : Fin (N - 1) → ↥P := fun i => ⟨r i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let Afun : Fin (N - 1) → ↥Q := fun i => η (giP i)
  have hgiP_sq : ∀ i, giP i * giP i = 1 := by
    intro i
    apply Subtype.ext
    simpa [giP] using l04fD4_rsq L i
  have hAfun_sq : ∀ i, Afun i * Afun i = 1 := by
    intro i
    change η (giP i) * η (giP i) = 1
    rw [← map_mul, hgiP_sq i, map_one]
  have hcoord : ∀ (i : Fin (N - 1)) (u : ↥Tsub),
      (((Afun i : ↥Q) : ↥Tsub ≃ₗ[ZMod p] ↥Tsub) u : V) = r i (u : V) := by
    intro i u
    have h1 := l04fD4_restrict_apply Tsub
      (Subgroup.inclusion hA (Subgroup.inclusion hPA (giP i))) u
    simpa [Afun, η, ggLargeRho, MonoidHom.comp_apply, giP, Subgroup.inclusion] using h1
  have hrk : ∀ i, Module.finrank (ZMod p) (ggLinMove
      ((Afun i : ↥Q) : ↥Tsub ≃ₗ[ZMod p] ↥Tsub)) = 1 :=
    fun i => l04fD4_move_rank_one L Q Afun hcoord i
  have hclosure_giP : Subgroup.closure (Set.range giP) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hmap : Subgroup.map (Subgroup.subtype P) (Subgroup.closure (Set.range giP)) = P := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨giP i, ⟨i, rfl⟩, rfl⟩
    have hx : (x : V ≃ₗ[ZMod p] V) ∈
        Subgroup.map (Subgroup.subtype P) (Subgroup.closure (Set.range giP)) := by
      rw [hmap]
      exact x.2
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  let H : Subgroup (Equiv.Perm (Fin d)) :=
    Subgroup.closure (Set.range (fun i : Fin (N - 1) => π (Afun i)))
  have hHtop : H = ⊤ := by
    have hHrange : H = ψ.range := by
      have hrange : Set.range (fun i : Fin (N - 1) => π (Afun i)) = ψ '' Set.range giP := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨giP i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      calc H = Subgroup.closure (Set.range (fun i : Fin (N - 1) => π (Afun i))) := rfl
        _ = Subgroup.closure (ψ '' Set.range giP) := by rw [hrange]
        _ = Subgroup.map ψ (Subgroup.closure (Set.range giP)) :=
              (MonoidHom.map_closure ψ (Set.range giP)).symm
        _ = Subgroup.map ψ (⊤ : Subgroup ↥P) := by rw [hclosure_giP]
        _ = ψ.range := Subgroup.map_top ψ
    rw [hHrange]
    apply Subgroup.eq_top_of_card_eq
    calc Nat.card ↥(ψ.range) = Nat.card ↥P :=
          (Nat.card_congr (Equiv.ofInjective ψ hψinj)).symm
      _ = Nat.card (Equiv.Perm (Fin (N - 1 + 1))) := (Nat.card_congr eP.toEquiv).symm
      _ = Nat.card (Equiv.Perm (Fin d)) := by
            rw [Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin]
            congr 1
            have hd' : N - 1 + 1 = d := by rw [hdN]; have := L.N_ge; omega
            exact hd'
  have htrans : ∀ i, ∃ i0 j0 : Fin d, i0 ≠ j0 ∧ π (Afun i) = Equiv.swap i0 j0 ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ((Afun i : ↥Q) : ↥Tsub ≃ₗ[ZMod p] ↥Tsub) (b i0) = c • b j0 := by
    intro i
    rcases l04fD4_monomial_involution L Q b hπ (hAfun_sq i) (hrk i) with h1 | h
    · exfalso
      have hne : π (Afun i) ≠ 1 := by
        intro hpi
        have hmem : giP i ∈ ψ.ker := by
          show ψ (giP i) = 1
          show π (η (giP i)) = 1
          exact hpi
        rw [hψker_bot, Subgroup.mem_bot] at hmem
        have hri1 : r i = 1 := by
          have := congrArg (fun z : ↥P => (z : V ≃ₗ[ZMod p] V)) hmem
          simpa [giP] using this
        exact l04fD4_ri_ne_one L i hri1
      exact hne h1
    · obtain ⟨i0, j0, hi0j0, hswap, c, hc, hscal⟩ := h
      exact ⟨i0, j0, hi0j0, hswap, c, hc, hscal⟩
  let pp : Fin (N - 1) → Fin d := fun i => (htrans i).choose
  let qq : Fin (N - 1) → Fin d := fun i => (htrans i).choose_spec.choose
  have hswap : ∀ i, π (Afun i) = Equiv.swap (pp i) (qq i) :=
    fun i => (htrans i).choose_spec.choose_spec.2.1
  have hscal : ∀ i, ∃ c : ZMod p, c ≠ 0 ∧
      ((Afun i : ↥Q) : ↥Tsub ≃ₗ[ZMod p] ↥Tsub) (b (pp i)) = c • b (qq i) :=
    fun i => (htrans i).choose_spec.choose_spec.2.2
  have hfinle : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1 :=
    l04fD4_fixed_bound L Q b hπ hdN Afun hcoord pp qq hswap hscal hHtop hTtop
  exact absurd (le_trans two hfinle) (Nat.not_succ_le_self 1)

end CFSG.StandardType

end
