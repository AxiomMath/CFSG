module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.CoprimeFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped commutatorElement

namespace P2251i

section Counting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_modEq_card_fix (f : Module.End (ZMod 2) V) {r : ℕ} (hr : r.Prime) (hf : f ^ r = 1)
    {S : Submodule (ZMod 2) V} (hS : ∀ s ∈ S, f s ∈ S) :
    Nat.card S ≡ Nat.card {v : V // v ∈ S ∧ f v = v} [MOD r] := by
  obtain ⟨fS, hfS⟩ : ∃ fS : S → S, ∀ s, (fS s : V) = f s := ⟨fun s => ⟨f s, hS s s.2⟩, fun _ => rfl⟩
  have hit : ∀ (n : ℕ) (s : S), ((fS^[n] s : S) : V) = (f ^ n) s := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', hfS, ih, pow_succ', Module.End.mul_apply]
  have hid : fS^[r] = id := funext fun s => Subtype.ext (by simp [hit, hf])
  have h := CFSG.EvenSporadicStandard.TwoB.card_modEq_card_fixedPoints_of_iterate_eq_id hr hid
  have e : Function.fixedPoints fS ≃ {v : V // v ∈ S ∧ f v = v} :=
    { toFun := fun s => ⟨s.1.1, s.1.2, by
        rw [← hfS]
        exact congrArg Subtype.val (Function.mem_fixedPoints_iff.1 s.2)⟩
      invFun := fun v => ⟨⟨v.1, v.2.1⟩, Function.mem_fixedPoints_iff.2 (Subtype.ext (by rw [hfS]; exact v.2.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Nat.card_congr e] at h

theorem exists_fixed_not (f : Module.End (ZMod 2) V) {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hf : f ^ r = 1)
    {W B : Submodule (ZMod 2) V} (hBW : B ≤ W) (hfW : ∀ w ∈ W, f w ∈ W) (hfB : ∀ b ∈ B, f b ∈ B)
    (hcard : Nat.card W = 16 * Nat.card B) {P : V → Prop} (hP : ∀ v ∈ W, P v → v ∈ B) :
    ∃ v ∈ W, f v = v ∧ ¬ P v := by
  by_contra hcon
  push Not at hcon
  have hW := card_modEq_card_fix f hr hf hfW
  have hB := card_modEq_card_fix f hr hf hfB
  have heq : Nat.card {v : V // v ∈ W ∧ f v = v} = Nat.card {v : V // v ∈ B ∧ f v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h => ⟨hP v h.1 (hcon v h.1 h.2), h.2⟩, fun h => ⟨hBW h.1, h.2⟩⟩)
  rw [heq, hcard] at hW
  have h15 : r ∣ 15 * Nat.card B := by
    have h2 := (Nat.modEq_iff_dvd' (by omega : Nat.card B ≤ 16 * Nat.card B)).1 (hW.trans hB.symm).symm
    rwa [show 16 * Nat.card B - Nat.card B = 15 * Nat.card B by omega] at h2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h15
  rcases (Nat.Prime.dvd_mul hr).1 h15 with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 (show r ∣ 3 * 5 from h) with h3 | h5
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h5) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)) (by omega)

end Counting

theorem card_eq_mul_card {V Y : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup Y] (ψ : V →+ Y)
    {W B : Submodule (ZMod 2) V} (hBW : B ≤ W) (hB : ∀ x ∈ B, ψ x = 0) (hW : ∀ x ∈ W, ψ x = 0 → x ∈ B)
    {Q : Y → Prop} (hQ : ∀ x ∈ W, Q (ψ x)) (hQ' : ∀ y, Q y → ∃ x ∈ W, ψ x = y) :
    Nat.card W = Nat.card {y // Q y} * Nat.card B := by
  let f : W →+ Y := ψ.comp W.subtype.toAddMonoidHom
  have e1 : f.range ≃ {y // Q y} := Equiv.subtypeEquivRight fun y =>
    ⟨fun hy => by
      obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.1 hy
      exact hQ w w.2,
    fun hy => by
      obtain ⟨x, hx, rfl⟩ := hQ' y hy
      exact AddMonoidHom.mem_range.2 ⟨⟨x, hx⟩, rfl⟩⟩
  have e2 : f.ker ≃ B :=
    { toFun := fun w => ⟨w.1.1, hW _ w.1.2 (AddMonoidHom.mem_ker.1 w.2)⟩
      invFun := fun b => ⟨⟨b.1, hBW b.2⟩, AddMonoidHom.mem_ker.2 (hB _ b.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← AddSubgroup.card_ker_mul_card_range f, Nat.card_congr e1, Nat.card_congr e2, mul_comm]

theorem card_sum_eq_zero : Nat.card {y : Fin 5 → ZMod 2 // ∑ i, y i = 0} = 16 := by
  let s : (Fin 5 → ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' (fun y => ∑ i, y i) fun a b => by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hs : Function.Surjective s := fun t => ⟨Pi.single 0 t, by simp [s]⟩
  have h := AddSubgroup.card_ker_mul_card_of_surjective hs
  have e : s.ker ≃ {y : Fin 5 → ZMod 2 // ∑ i, y i = 0} :=
    Equiv.subtypeEquivRight fun y => AddMonoidHom.mem_ker
  rw [Nat.card_congr e, Nat.card_zmod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 5),
    Fintype.card_fin] at h
  omega

theorem two_pow_eq_four {n : ℕ} (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 60) : 2 ^ n = 4 := by
  have hn : n < 3 := by
    by_contra hn
    have h8 : 8 ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 3 ≤ n)
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    omega
  interval_cases n <;> simp_all

theorem sec_facts {X V : Type} [Group X] [Finite X] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) X V} {H : Subgroup X} {W C : Submodule (ZMod 2) V}
    (hsh : Shape148 ρ H W C) (hH : IsL2Ev ↥H 2 ∨ IsS5 ↥H) :
    Nat.card W = 16 * Nat.card ↥(W ⊓ C) ∧ ∀ v ∈ W, (∀ g ∈ ⁅H, H⁆, ρ g v = v) → v ∈ W ⊓ C := by
  rcases hH with h2 | h5
  · obtain ⟨n, -, F, _, _, hF, -, -, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := P22x.natL2_of_shape148 ρ H W C h2 hsh
    have hH60 : Nat.card ↥H = 60 := by norm_num [P22x.card_of_isL2Ev h2]
    have h60 : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 60 := by
      rw [← hF, ← CFSG.Open.StatedAPI.card_statedSL_two, ← Nat.card_congr φ.toEquiv, hH60]
    have hcard : Nat.card F = 4 := hF.trans (two_pow_eq_four h60)
    have hHH : ⁅H, H⁆ = H := LayerShape22.commutator_eq_self (Or.inl ⟨2, le_rfl, h2⟩)
    refine ⟨?_, fun v hv hfix => hψA v hv ?_⟩
    · rw [card_eq_mul_card ψ hBA hψB hψA (Q := fun _ => True) (fun _ _ => trivial) (fun y _ => hψs y),
        Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), P22x.card_vec2, hcard]
      norm_num
    · rw [hHH] at hfix
      have key : ∀ (i j : Fin 2) (hij : i ≠ j), ψ v + Pi.single i (1 * ψ v j) = ψ v := by
        intro i j hij
        have := hψφ (φ.symm (P22x.sl2Transvection i j hij 1)) v hv
        rw [hfix _ (φ.symm (P22x.sl2Transvection i j hij 1)).2, MulEquiv.apply_symm_apply,
          P22x.sl2Transvection_mulVec] at this
        exact this.symm
      have h01 := congrFun (key 0 1 (by decide)) 0
      have h10 := congrFun (key 1 0 (by decide)) 1
      simp at h01 h10
      funext k
      fin_cases k <;> simp [h01, h10]
  · have hc120 : Nat.card ↥H = 120 := by
      obtain ⟨e⟩ := h5
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have h168 : ∀ e : ↥H ≃* ↥(StatedSL 3 (ZMod 2)), False := fun e => by
      have : Nat.card ↥H = 168 := by
        rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, Nat.card_zmod]
        norm_num
      omega
    obtain ⟨-, -, hBA, φ, ψ, hψB, hψA, hψ0, hψs, hψφ⟩ : SecNatS5 ρ H W (W ⊓ C) := by
      rcases hsh with ⟨n, -, F, _, _, hF, -, -, -, φ, -⟩ | ⟨-, -, -, φ, -⟩ | ⟨Ai, hAi, -⟩ | h
      · exfalso
        have : Nat.card ↥H = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
          rw [Nat.card_congr φ.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF]
        exact (P22x.sl2_order_ne n).2 (this.symm.trans hc120)
      · exact (h168 φ).elim
      · obtain ⟨-, -, -, φ, -⟩ := (hAi 0).2.2
        exact (h168 φ).elim
      · exact h
    refine ⟨?_, fun v hv hfix => hψA v hv ?_⟩
    · rw [card_eq_mul_card ψ hBA hψB hψA (Q := fun y => ∑ i, y i = 0) hψ0 hψs, card_sum_eq_zero]
    · have hc : ∀ σ τ : Equiv.Perm (Fin 5), ∀ j, ψ v j = ψ v ((σ * τ * σ⁻¹ * τ⁻¹).symm j) := by
        intro σ τ j
        have hg : ((φ.symm (σ * τ * σ⁻¹ * τ⁻¹) : ↥H) : X) ∈ ⁅H, H⁆ := by
          have := commutator_mem_commutator (φ.symm σ).2 (φ.symm τ).2
          simpa [commutatorElement_def] using this
        have := hψφ (φ.symm (σ * τ * σ⁻¹ * τ⁻¹)) v hv
        rw [hfix _ hg, MulEquiv.apply_symm_apply] at this
        exact congrFun this j
      have e1 : ψ v 1 = ψ v 0 := (hc (Equiv.swap 1 2) (Equiv.swap 0 1) 1).trans (congrArg (ψ v) (by decide))
      have e2 : ψ v 2 = ψ v 1 := (hc (Equiv.swap 1 2) (Equiv.swap 0 1) 2).trans (congrArg (ψ v) (by decide))
      have e3 : ψ v 3 = ψ v 2 := (hc (Equiv.swap 3 4) (Equiv.swap 2 3) 3).trans (congrArg (ψ v) (by decide))
      have e4 : ψ v 4 = ψ v 3 := (hc (Equiv.swap 3 4) (Equiv.swap 2 3) 4).trans (congrArg (ψ v) (by decide))
      have hs := hψ0 v hv
      rw [Fin.sum_univ_five, e4, e3, e2, e1, show ∀ x : ZMod 2, x + x + x + x + x = x by decide] at hs
      funext k
      fin_cases k <;> simp [hs, e1, e2, e3, e4]

end P2251i

open P2251i

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251i_exists_mem (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (hH : H1930 D)
    (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m}
    (hi : IsL2Ev ↥(Nb i) 2 ∨ IsS5 ↥(Nb i)) {K A : Subgroup G} (hK : K ∈ calC D.M)
    (hKb : mbarImage D.M D.U K = ⁅Nb i, Nb i⁆) (hAM : A ≤ D.M) (hA : (Nat.card A).Prime)
    (hA7 : 7 ≤ Nat.card A) (hc : ⁅A, K⁆ ≤ pCoreOf 2 K) :
    ∃ u ∈ D.U, u ∈ centralizer (A : Set G) ∧ ∃ g ∈ K, g * u * g⁻¹ ≠ u := by
  have hV := P22x.uc22p22xf_hV D
  have hOU : pCoreOf 2 D.M ≤ centralizer (D.U : Set G) :=
    le_centralizer_iff.1 ((uc22p22c_U_facts D).1.trans inf_le_right)
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 D.M := uc22p22r_pCoreOf_le_of_isSubnormal hK.1
  obtain ⟨Umod, _, _, _, e, ρ, hcm⟩ := uc22br4_exists_conjModule D.M D.U hV (P22x.uc22p22xf_hel D)
  obtain ⟨-, hsh⟩ := h3 hH c m Nb hNb Umod e ρ hcm
  haveI : Fact (Nat.card A).Prime := ⟨hA⟩
  haveI : IsCyclic A := isCyclic_of_prime_card rfl
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥A)
  obtain ⟨am, hamv⟩ : ∃ am : ↥D.M, (am : G) = a := ⟨⟨a, hAM a.2⟩, rfl⟩
  obtain ⟨ab, hab⟩ : ∃ ab : MBar D.M D.U, QuotientGroup.mk' (kerAct D.M D.U).normalCore am = ab := ⟨_, rfl⟩
  have hamr : am ^ Nat.card A = 1 := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val (pow_card_eq_one' (G := ↥A) (x := a))
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, hamv] at h1 ⊢
    exact h1
  have hfr : ρ ab ^ Nat.card A = 1 := by
    rw [← hab, ← map_pow, ← map_pow, hamr, map_one, map_one]
  have hcomm : ∀ y ∈ mbarImage D.M D.U K, ab * y = y * ab := by
    intro y hy
    obtain ⟨k', hk', rfl⟩ := mem_map.1 hy
    have h1 : ((⁅am, k'⁆ : ↥D.M) : G) ∈ centralizer (D.U : Set G) := by
      have : ((⁅am, k'⁆ : ↥D.M) : G) = ⁅(a : G), (k' : G)⁆ := by rw [← hamv]; rfl
      rw [this]
      exact hOU (hOK (hc (commutator_mem_commutator a.2 (mem_subgroupOf.1 hk'))))
    have h2 : QuotientGroup.mk' (kerAct D.M D.U).normalCore ⁅am, k'⁆ = 1 :=
      (uc22br_gt_mk_eq_one_iff hV _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hab] at h2
    exact h2
  have hNn := uc22p22ya_nbar_normal D
  have habN : ab ∈ normalizer ((mbarImage D.M D.U (proofN D) : Subgroup (MBar D.M D.U)) : Set (MBar D.M D.U)) := by
    rw [normalizer_eq_top_iff.2 hNn]
    exact mem_top _
  obtain ⟨τ, hτ⟩ := P22y.exists_perm hNb.1 (fun k => P22w.isIndecomposable_of_factorShape22 (hNb.2 k))
    (fun k => P22w.center_eq_bot_of_factorShape22 (hNb.2 k)) habN
  have hK2 : IsL2Ev ↥⁅Nb i, Nb i⁆ 2 := by
    rcases hi with h | h
    · rwa [LayerShape22.commutator_eq_self (Or.inl ⟨2, le_rfl, h⟩ : LayerShape22 ↥(Nb i))]
    · exact P2251b.isL2Ev_two_commutator_of_isS5 h
  have hKτ : ⁅Nb i, Nb i⁆ ≤ Nb (τ i) := by
    intro y hy
    rw [← hτ i]
    refine mem_map.2 ⟨y, Subgroup.commutator_le_self (Nb i) hy, ?_⟩
    show ab * y * ab⁻¹ = y
    rw [hcomm y (by rw [hKb]; exact hy), mul_inv_cancel_right]
  have hτi : τ i = i := by
    by_contra hne
    have hle : ⁅Nb i, Nb i⁆ ≤ ⊥ := (hNb.1.2.2 i).le.trans' (le_inf (Subgroup.commutator_le_self (Nb i))
      fun y hy => Subgroup.mem_iSup_of_mem (τ i)
        (Subgroup.mem_iSup_of_mem (show τ i ∈ {j | j ≠ i} from hne) (hKτ hy)))
    have h60 := P22x.card_of_isL2Ev hK2
    rw [le_bot_iff.1 hle, card_bot] at h60
    norm_num at h60
  have hconj : ∀ y ∈ Nb i, ab * y * ab⁻¹ ∈ Nb i := fun y hy => by
    rw [← hτi, ← hτ i]
    exact ⟨y, hy, rfl⟩
  have hfI : ∀ x ∈ modI D ρ, ρ ab x ∈ modI D ρ :=
    P22x.commOn_invariant (A := mbarImage D.M D.U (proofN D)) (U := ⊤)
      (fun y hy => hNn.conj_mem y hy ab) fun _ _ => trivial
  have hfW : ∀ x ∈ commOn ρ (Nb i) (modI D ρ), ρ ab x ∈ commOn ρ (Nb i) (modI D ρ) :=
    P22x.commOn_invariant hconj hfI
  have hfC : ∀ x ∈ fixSub ρ (mbarImage D.M D.U (proofN D)),
      ρ ab x ∈ fixSub ρ (mbarImage D.M D.U (proofN D)) := by
    intro x hx
    rw [mem_fixSub] at hx ⊢
    intro n hn
    have h1 : ab⁻¹ * n * ab ∈ mbarImage D.M D.U (proofN D) := by
      simpa using hNn.conj_mem n hn ab⁻¹
    calc ρ n (ρ ab x) = ρ (n * ab) x := by rw [map_mul ρ n ab, Module.End.mul_apply]
      _ = ρ (ab * (ab⁻¹ * n * ab)) x := by rw [show ab * (ab⁻¹ * n * ab) = n * ab by group]
      _ = ρ ab (ρ (ab⁻¹ * n * ab) x) := by rw [map_mul ρ ab (ab⁻¹ * n * ab), Module.End.mul_apply]
      _ = ρ ab x := by rw [hx _ h1]
  have hfB : ∀ x ∈ commOn ρ (Nb i) (modI D ρ) ⊓ modCI D ρ,
      ρ ab x ∈ commOn ρ (Nb i) (modI D ρ) ⊓ modCI D ρ := fun x hx =>
    ⟨hfW x hx.1, hfI x hx.2.1, hfC x hx.2.2⟩
  obtain ⟨hcard, hP⟩ := sec_facts (hsh i) hi
  obtain ⟨v, -, hfv, hPv⟩ := exists_fixed_not (ρ ab) hA hA7 hfr inf_le_left hfW hfB hcard
    (P := fun v => ∀ g ∈ ⁅Nb i, Nb i⁆, ρ g v = v) hP
  push Not at hPv
  obtain ⟨g', hg', hgv⟩ := hPv
  rw [← hKb] at hg'
  obtain ⟨k', hk', rfl⟩ := mem_map.1 hg'
  have hau : (a : G) * P22x.iota e v * (a : G)⁻¹ = P22x.iota e v := by
    have := P22x.iota_rho hV e ρ hcm am v
    rw [show (QuotientGroup.mk am : MBar D.M D.U) = ab from hab, hfv, hamv] at this
    exact this.symm
  refine ⟨P22x.iota e v, P22x.iota_mem e v, ?_, (k' : G), mem_subgroupOf.1 hk', fun h => hgv ?_⟩
  · rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (ha ⟨x, hx⟩)
    have hx' : (a : G) ^ j = x := by simpa using congrArg Subtype.val hj
    rw [← hx']
    exact (Commute.zpow_left (mul_inv_eq_iff_eq_mul.1 hau) j).eq
  · apply P22x.iota_injective e
    rw [QuotientGroup.mk'_apply, P22x.iota_rho hV e ρ hcm k' v, h]

theorem uc22p2251i_commutator_ne_bot (D : Data G) {K A : Subgroup G} (hK : K ∈ calC D.M)
    (hKN : D.M ≤ normalizer (K : Set G)) (hcov : K = Opp 3 (K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 K)
    {u : G} (huU : u ∈ D.U) (huA : u ∈ centralizer (A : Set G)) {g : G} (hgK : g ∈ K)
    (hgu : g * u * g⁻¹ ≠ u) :
    ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ Opp 3 (K ⊓ centralizer (A : Set G)),
      Opp 3 (K ⊓ centralizer (A : Set G))⁆ ≠ ⊥ := by
  have hV := P22x.uc22p22xf_hV D
  have hUf := uc22p22c_U_facts D
  have hOU : pCoreOf 2 D.M ≤ centralizer (D.U : Set G) := le_centralizer_iff.1 (hUf.1.trans inf_le_right)
  have hOK : pCoreOf 2 K ≤ centralizer (D.U : Set G) := (uc22p22r_pCoreOf_le_of_isSubnormal hK.1).trans hOU
  have hKM : K ≤ D.M := hK.1.le
  have huM : u ∈ D.M := Subgroup.map_subtype_le (CFSG.pCore 2 ↥D.M) (hUf.1 huU).1
  obtain ⟨x, hxY, k, hxk, hxu⟩ : ∃ x ∈ K ⊓ centralizer (A : Set G), ∃ k : ℕ, orderOf x = 3 ^ k ∧
      x * u * x⁻¹ ≠ u := by
    by_contra hcon
    push Not at hcon
    have hX : Opp 3 (K ⊓ centralizer (A : Set G)) ≤ centralizer ({u} : Set G) := by
      unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      refine (closure_le _).2 fun x hx => ?_
      obtain ⟨hxY, k, hxk⟩ := hx
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.1 (hcon x hxY k hxk)
    have hO : pCoreOf 2 K ≤ centralizer ({u} : Set G) := fun y hy =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hOK hy) u huU).symm
    have hgc := mem_centralizer_singleton_iff.1 ((hcov.le.trans (sup_le hX hO)) hgK)
    exact hgu (by rw [hgc, mul_inv_cancel_right])
  have hxM : x ∈ D.M := hKM (mem_inf.1 hxY).1
  have hxX : x ∈ Opp 3 (K ⊓ centralizer (A : Set G)) := subset_closure ⟨hxY, k, hxk⟩
  have hconjY : ∀ w ∈ D.M, w ∈ centralizer (A : Set G) → ∀ h ∈ K ⊓ centralizer (A : Set G),
      w * h * w⁻¹ ∈ K ⊓ centralizer (A : Set G) := fun w hwM hwA h hh =>
    mem_inf.2 ⟨(mem_normalizer_iff.1 (hKN hwM) h).1 (mem_inf.1 hh).1,
      mul_mem (mul_mem hwA (mem_inf.1 hh).2) (inv_mem hwA)⟩
  have huN : u ∈ normalizer ((K ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hconjY u huM huA h, fun hh => ?_⟩
    have := hconjY u⁻¹ (inv_mem huM) (inv_mem huA) _ hh
    rwa [inv_inv, show u⁻¹ * (u * h * u⁻¹) * u = h by group] at this
  obtain ⟨w, hw⟩ : ∃ w, w = x * u * x⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hwU : w ∈ D.U := hw ▸ mul_mem (uc22br_gt_conj_mem hV hxM huU) (inv_mem huU)
  have hwX : w ∈ Opp 3 (K ⊓ centralizer (A : Set G)) := by
    rw [hw, show x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) by group]
    exact mul_mem hxX (P2251h.conj_mem_opp huN 3 (inv_mem hxX))
  intro hbot
  have hwx : ⁅w, x⁆ = 1 := by
    have := commutator_mem_commutator (mem_inf.2 ⟨hUf.1 hwU, hwX⟩) hxX
    rwa [hbot, mem_bot] at this
  have hcomm : Commute w x := commutatorElement_eq_one_iff_commute.1 hwx
  have hxu' : x * u * x⁻¹ = w * u := by rw [hw]; group
  have hpow : ∀ j : ℕ, x ^ j * u * (x ^ j)⁻¹ = w ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hwj : x * w ^ j * x⁻¹ = w ^ j := by rw [(hcomm.symm.pow_right j).eq, mul_inv_cancel_right]
      calc x ^ (j + 1) * u * (x ^ (j + 1))⁻¹ = x * (x ^ j * u * (x ^ j)⁻¹) * x⁻¹ := by group
        _ = x * (w ^ j * u) * x⁻¹ := by rw [ih]
        _ = (x * w ^ j * x⁻¹) * (x * u * x⁻¹) := by group
        _ = w ^ j * (w * u) := by rw [hwj, hxu']
        _ = w ^ (j + 1) * u := by group
  have hx3 : x ^ (3 ^ k) = 1 := by rw [← hxk]; exact pow_orderOf_eq_one x
  have hw3 : w ^ (3 ^ k) = 1 := by
    have := hpow (3 ^ k)
    rw [hx3, one_mul, inv_one, mul_one] at this
    exact right_eq_mul.1 this
  have hw1 : w = 1 := by
    have h1 : orderOf w ∣ Nat.gcd 2 (3 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hUf.2.2 w hwU)) (orderOf_dvd_of_pow_eq_one hw3)
    rwa [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h1
  exact hxu (mul_inv_eq_one.1 (hw ▸ hw1))

theorem uc22p2251i_r923_hyp (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (hH : H1930 D)
    (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m}
    (hi : IsL2Ev ↥(Nb i) 2 ∨ IsS5 ↥(Nb i)) {K A : Subgroup G} (hK : K ∈ calC D.M)
    (hKb : mbarImage D.M D.U K = ⁅Nb i, Nb i⁆) (hKN : D.M ≤ normalizer (K : Set G)) (hAM : A ≤ D.M)
    (hA : (Nat.card A).Prime) (hA7 : 7 ≤ Nat.card A) (hc : ⁅A, K⁆ ≤ pCoreOf 2 K)
    (hcov : K = Opp 3 (K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 K) :
    ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ Opp 3 (K ⊓ centralizer (A : Set G)),
      Opp 3 (K ⊓ centralizer (A : Set G))⁆ ≠ ⊥ := by
  obtain ⟨u, huU, huA, g, hgK, hgu⟩ := uc22p2251i_exists_mem D Ch h3 hH c hNb hi hK hKb hAM hA hA7 hc
  exact uc22p2251i_commutator_ne_bot D hK hKN hcov huU huA hgK hgu

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
