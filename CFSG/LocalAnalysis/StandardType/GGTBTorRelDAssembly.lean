module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDRoot
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrameSigned
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift

public section

namespace CFSG.StandardType

namespace RelD

open CFSG.Assembly Multiplicative

variable {G : Type} [Group G] {μ : Type} [CommGroup μ]

theorem ggTorusTorData_of_blockModel {M p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hM : Odd M)
    (hr : 2 ≤ r) (hcenter : Subgroup.center G = ⊥)
    (l : μ ≃* Multiplicative (ZMod M))
    (ψ : (Fin r → μ) →* G) (hψ : Function.Injective ψ)
    (E : Subgroup G) (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ ψ.range)
    (ζ : μ) (hζo : orderOf ζ = p)
    (w : Fin r → G)
    (hswap : ∀ (k : Fin r) (hk : k.val + 1 < r) (x : Fin r → μ),
      w k * ψ x * (w k)⁻¹ = ψ (x ∘ Equiv.swap k ⟨k.val + 1, hk⟩))
    (hlast : ∀ (k : Fin r), k.val + 1 = r → ∀ x : Fin r → μ,
      w k * ψ x * (w k)⁻¹ = ψ (Function.update x k (x k)⁻¹))
    (hcomm : ∀ g : G, (∀ e ∈ E, g * e = e * g) → ∀ x, Commute (ψ x) g)
    (htors : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ^ M = 1 → g ∈ ψ.range)
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set G), ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ℤ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ x : Fin r → μ, x ^ p = 1 →
        g * ψ x * g⁻¹ = ψ (fun i => x (π.symm i) ^ ε (π.symm i))) :
    GGTorusTorData M r (CartanMatrix.B r) (CoxeterMatrix.B r) G (scalarA E) := by
  classical
  have hpp : p.Prime := Fact.out
  have : NeZero p := ⟨hpp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hpp.ne_one hζo.symm
  have hj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  let φ : (Fin r → μ) →* G := ψ.comp blockOfRoot.toMonoidHom
  have hφ : Function.Injective φ := hψ.comp blockOfRoot.injective
  have hφapply : ∀ a, φ a = ψ (blockOfRoot a) := fun _ => rfl
  have hφrange : φ.range = ψ.range := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨blockOfRoot.symm x, by rw [hφapply, MulEquiv.apply_symm_apply]⟩
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_B (M := M) (n := r) (by omega) hM
  have hE' : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range := by
    intro g
    rw [hφrange]
    exact hE g
  have hnformula : ∀ k (a : Fin r → μ),
      w k * φ a * (w k)⁻¹ = φ a * (φ (corTuple (CartanMatrix.B r).transpose k (a k)))⁻¹ := by
    intro k a
    rw [← map_inv, ← map_mul, hφapply, hφapply]
    by_cases hk : k.val + 1 < r
    · rw [hswap k hk, blockOfRoot_reflect_of_lt a k hk]
    · have hk' : k.val + 1 = r := by omega
      rw [hlast k hk', blockOfRoot_reflect_last a k hk']
  let z : Multiplicative (ZMod p) →* μ := TableBSymp.zmodPowHom hζp
  let ι : (Fin r → Multiplicative (ZMod p)) →* G := ψ.comp (z.compLeft (Fin r))
  have hιapply : ∀ f, ι f = ψ (fun i => z (f i)) := fun _ => rfl
  have hz : Function.Injective z := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, TableBSymp.zmodPowHom_apply] at ha
    have hlt : (toAdd a).val < p := ZMod.val_lt _
    have hdvd := orderOf_dvd_of_pow_eq_one ha
    rw [hζo] at hdvd
    have h0 : (toAdd a).val = 0 := by
      rcases Nat.eq_zero_or_pos (toAdd a).val with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hdvd) (by omega)
    rw [Subgroup.mem_bot, ← ofAdd_toAdd a, (ZMod.val_eq_zero _).mp h0, ofAdd_zero]
  have hι : Function.Injective ι := hψ.comp fun f g h => funext fun i => hz (congrFun h i)
  have hzpow : ∀ x : μ, x ^ p = 1 → ∃ a, z a = x := by
    haveI : NeZero M := ⟨fun h => by subst h; exact (by decide : ¬ Odd 0) hM⟩
    haveI : Finite μ := Finite.of_equiv _ l.toEquiv.symm
    haveI : IsCyclic μ := isCyclic_of_surjective l.symm.toMonoidHom l.symm.surjective
    letI : Fintype μ := Fintype.ofFinite μ
    have hfin : IsOfFinOrder ζ := isOfFinOrder_of_finite ζ
    intro x hx
    have hxz : x ∈ Subgroup.zpowers ζ := by
      by_contra hxn
      have hsub : insert x ((Subgroup.zpowers ζ : Set μ).toFinset) ⊆
          Finset.univ.filter (fun a : μ => a ^ p = 1) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · simpa using hx
        · rw [Set.mem_toFinset, SetLike.mem_coe] at ha
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simpa using hxn)] at hcard
      have h1 : ((Subgroup.zpowers ζ : Set μ).toFinset).card = p := by
        rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
        change Nat.card (Subgroup.zpowers ζ) = p
        rw [Nat.card_zpowers, hζo]
      have h2 := IsCyclic.card_pow_eq_one_le (α := μ) (n := p) hpp.pos
      omega
    obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hxz
    refine ⟨ofAdd (n : ZMod p), ?_⟩
    rw [TableBSymp.zmodPowHom_natCast]
    exact hn
  have hzp : ∀ a, z a ^ p = 1 := fun a => by
    rw [← map_pow, ← ofAdd_toAdd a, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      ofAdd_zero, map_one]
  have hιrange : ι.range = E := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩
      refine (hE _).mpr ⟨?_, ⟨_, (hιapply f).symm⟩⟩
      rw [hιapply, ← map_pow]
      convert map_one ψ using 2
      funext i
      exact hzp (f i)
    · intro hg
      obtain ⟨hgp, x, rfl⟩ := (hE g).mp hg
      have hxp : x ^ p = 1 := hψ (by rw [map_pow, hgp, map_one])
      choose f hf using fun i => hzpow (x i) (by simpa using congrFun hxp i)
      exact ⟨f, by rw [hιapply]; congr 1; funext i; exact hf i⟩
  have hnι : ∀ (i : Fin r) (f : Fin r → Multiplicative (ZMod p)),
      w i * ι f * (w i)⁻¹ = ι (SpJoin.spReflPerm r p i f) := by
    intro i f
    rw [hιapply, hιapply]
    by_cases hi : i.val + 1 < r
    · rw [hswap i hi, SpJoin.spReflPerm_of_lt r p i hi]
      rfl
    · rw [hlast i (by omega), SpJoin.spReflPerm_of_not_lt r p i hi]
      congr 1
      funext t
      simp only [SpJoin.coordInv_apply, Function.update_apply]
      split_ifs with h
      · subst h
        rw [map_inv]
      · rfl
  have hNι : ∀ g ∈ Subgroup.normalizer (E : Set G), ∃ σ ∈ SpJoin.spSignedGroup r p,
      ∀ f, g * ι f * g⁻¹ = ι (σ f) := by
    intro g hg
    obtain ⟨π, ε, hε, hgx⟩ := hN g hg
    obtain ⟨σ, hσ, hσf⟩ := signedPerm_mem_spSignedGroup (p := p) π ε hε
    refine ⟨σ, hσ, fun f => ?_⟩
    rw [hιapply, hgx _ (by funext i; simpa using hzp (f i)), hιapply, hσf]
    congr 1
    funext i
    rw [map_zpow]
  obtain ⟨hnN, -, eW, heW⟩ := exists_markedWeylB_ggAutomizer hp2 hr E ι hι hιrange w hnι hNι
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_innerImage E hj w hnN eW heW
  let ρ : (CoxeterMatrix.B r).Group →* MulAut ↥(scalarA E) :=
    (ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E)).subtype.comp eA.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp eA.injective
  have hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro hx
      obtain ⟨g, hg⟩ := eA.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ ((CoxeterMatrix.B r).simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (w k) * (a : MulAut G) * (MulAut.conj (w k))⁻¹ := by
    intro k a
    change (((eA ((CoxeterMatrix.B r).simple k) : MulAut ↥(scalarA E)) a : ↥(scalarA E)) :
      MulAut G) = _
    rw [heA k, ggConjAut_apply]
  let Tsc : Subgroup G := Subgroup.centralizer (E : Set G)
  have hmemT : ∀ t ∈ Tsc, ∀ e ∈ E, t * e = e * t := fun t ht e he =>
    ((Subgroup.mem_centralizer_iff.mp ht) e he).symm
  refine ggTorusTorData_of_rootCoordinates_tsc l φ hφ (CartanMatrix.B r) B hCB hBC ?_ Tsc ?_ ?_ ?_
    E hE' ζ hζp hζ1 w hnA hnformula ?_ (CoxeterMatrix.B r) ρ hρ hρrange hρsimple
  · intro a ha
    rw [hcenter, Subgroup.mem_bot] at ha
    exact hφ (by rw [ha, map_one])
  · intro a t ht
    exact hcomm t (hmemT t ht) (blockOfRoot a)
  · intro t ht htM
    rw [hφrange]
    exact htors t (hmemT t ht) htM
  · intro c hc _
    rw [hcenter, Subgroup.mem_bot] at hc
    rw [hc]
    exact one_mem _
  · intro g hg
    refine Subgroup.mem_sup_left (Subgroup.mem_centralizer_iff.mpr fun e he => ?_)
    have h := hg e he
    rw [hcenter, Subgroup.mem_bot] at h
    calc e * g = (g * e * g⁻¹ * e⁻¹)⁻¹ * (g * e) := by group
      _ = g * e := by rw [h, inv_one, one_mul]

end RelD

end CFSG.StandardType
