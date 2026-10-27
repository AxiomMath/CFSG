module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section Conj

open TableBExc.E6Three

variable {K : Type} [Field K]

theorem hatAut_rootDiagUnit_eq_rootDiagAutHom {τ : Tag} (a : Fin τ.rank → Kˣ) :
    hatAut τ K ⟨rootDiagUnit τ a, rootDiagUnit_mem_hatGroup a⟩ = rootDiagAutHom τ K a := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [coe_hatAut_apply]
  exact (coe_rootDiagAut a g).symm

theorem card_le_mul_card_diagKernel_of_le_xHat {τ : Tag} {p : ℕ} [NeZero p] {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {S : Subgroup (WeylGroup τ)}
    {E : Subgroup (ModGL τ K)} [Finite E] (hE : IsElemAbelian p E) (hEX : E ≤ xHat τ K S) :
    ∃ A : Subgroup (WeylGroup τ), A ≤ S ∧ IsElemAbelian p A ∧
      (∀ a ∈ A, ∀ x : Fin τ.rank → ZMod p,
        rootDiagUnit τ (zetaVec ζ hζ x) ∈ E → adAct τ p a x = x) ∧
      Nat.card E ≤
        Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // rootDiagUnit τ (zetaVec ζ hζ x) ∈ E} ∧
      (A = ⊥ → ∀ e ∈ E, ∃ x, e = rootDiagUnit τ (zetaVec ζ hζ x)) := by
  have hEM : E ≤ monoHat τ K := hEX.trans (xHat_le_monoHat S)
  set ψE : E →* WeylGroup τ := (psiHat τ K).comp (Subgroup.inclusion hEM) with hψE
  have hψS : ∀ e : E, ψE e ∈ S := fun e => (mem_xHat.mp (hEX e.2)).2
  have hker : ∀ e : E, ψE e = 1 → ∃ x, (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) := by
    intro e he
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (x := Subgroup.inclusion hEM e) he
    have hb' : (e : ModGL τ K) = rootDiagUnit τ b := hb
    have hbp : b ^ p = 1 := by
      have h1 : (e : ModGL τ K) ^ p = 1 := hE.2 _ e.2
      rw [hb', rootDiagUnit_pow] at h1
      exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    obtain ⟨x, hx⟩ := exists_zetaVec_eq hζo hζ hbp
    exact ⟨x, by rw [hb', hx]⟩
  have hfix : ∀ (e₀ e : E) (x : Fin τ.rank → ZMod p),
      (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) → adAct τ p (ψE e₀) x = x := by
    intro e₀ e x hx
    have hc := conj_rootDiagUnit_of_mem_monoHat (Subgroup.inclusion hEM e₀) (zetaVec ζ hζ x)
    have hcomm : (e₀ : ModGL τ K) * e * (e₀ : ModGL τ K)⁻¹ = e := by
      rw [TableB.IsElemAbelian.comm hE e₀.2 e.2, mul_inv_cancel_right]
    rw [weylTuple_zetaVec] at hc
    have h2 : rootDiagUnit τ (zetaVec ζ hζ (adAct τ p (ψE e₀) x)) =
        rootDiagUnit τ (zetaVec ζ hζ x) := by
      rw [← hx, ← hcomm, hx]
      exact hc.symm
    exact zetaVec_injective hζo hζ (rootDiagUnit_injective h2)
  have hker_le :
      Nat.card ψE.ker ≤
        Nat.card {x : Fin τ.rank → ZMod p // rootDiagUnit τ (zetaVec ζ hζ x) ∈ E} := by
    choose xf hxf using fun e : ψE.ker => hker e e.2
    refine Nat.card_le_card_of_injective (fun e : ψE.ker =>
      (⟨xf e, ?_⟩ : {x : Fin τ.rank → ZMod p // rootDiagUnit τ (zetaVec ζ hζ x) ∈ E})) ?_
    · rw [← hxf e]
      exact (e : E).2
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have h1 := congrArg Subtype.val hab
      simp only at h1
      rw [hxf a, hxf b, h1]
  have hker_rootDiag :
      ∀ y : {x : Fin τ.rank → ZMod p // rootDiagUnit τ (zetaVec ζ hζ x) ∈ E},
        ψE ⟨rootDiagUnit τ (zetaVec ζ hζ y.1), y.2⟩ = 1 := by
    intro y
    exact psiHat_eq (mapsRootLines_rootDiagUnit (τ := τ) (K := K) (zetaVec ζ hζ y.1))
  have hXk_le :
      Nat.card {x : Fin τ.rank → ZMod p // rootDiagUnit τ (zetaVec ζ hζ x) ∈ E} ≤
        Nat.card ψE.ker := by
    refine Nat.card_le_card_of_injective (fun x =>
      (⟨⟨rootDiagUnit τ (zetaVec ζ hζ x.1), x.2⟩, hker_rootDiag x⟩ : ψE.ker)) ?_
    intro a b hab
    apply Subtype.ext
    have h1 := congrArg (fun e : ψE.ker => ((e : E) : ModGL τ K)) hab
    exact zetaVec_injective hζo hζ (rootDiagUnit_injective h1)
  have hcardker : Nat.card ψE.ker =
      Nat.card {x : Fin τ.rank → ZMod p // rootDiagUnit τ (zetaVec ζ hζ x) ∈ E} :=
    le_antisymm hker_le hXk_le
  refine ⟨ψE.range, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact hψS e
  · exact isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ψE
  · rintro a ⟨e₀, rfl⟩ x hx
    exact hfix e₀ ⟨rootDiagUnit τ (zetaVec ζ hζ x), hx⟩ x rfl
  · have hcardE := TableB.card_range_mul_card_ker ψE
    refine le_of_eq ?_
    rw [hcardE.symm, hcardker]
  · intro hbot e he
    have h1 : ψE ⟨e, he⟩ ∈ ψE.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact hker ⟨e, he⟩ h1

theorem exists_conj_kernel_fix_of_le_hatAut [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) :
    ∃ γ ∈ (hatAut .E6 K).range, ∃ A : Subgroup (WeylGroup .E6), IsElemAbelian 3 A ∧
      (∀ a ∈ A, ∀ x : Fin Tag.E6.rank → ZMod 3,
        diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj γ).toMonoidHom →
          adAct .E6 3 a x = x) ∧
      Nat.card X ≤ Nat.card A * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj γ).toMonoidHom} ∧
      (A = ⊥ → X.map (MulAut.conj γ).toMonoidHom ≤ vAd ζ hζ) := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  set κ := hatAut .E6 K with hκ
  have hκrd : ∀ a : Fin Tag.E6.rank → Kˣ,
      κ ⟨rootDiagUnit .E6 a, rootDiagUnit_mem_hatGroup a⟩ = rootDiagAutHom .E6 K a := by
    intro a
    rw [hκ]
    exact hatAut_rootDiagUnit_eq_rootDiagAutHom a
  set Y : Subgroup (hatGroup .E6 K) := X.comap κ with hY
  set f : Y →* X := (κ.comp Y.subtype).codRestrict X (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hXI hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hXp : IsPGroup 3 (⊤ : Subgroup X) := fun g => by
    obtain ⟨k, hk⟩ := TableB.isPGroup_of_isElemAbelian hX ⟨g.1, g.1.2⟩
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hXp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPX : P.map κ = X := by
    have hcomp : κ.comp Y.subtype = X.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3) hP3
  set P' := P.map (MulAut.conj c).toMonoidHom with hP'
  set E : Subgroup (ModGL .E6 K) := P'.map (hatGroup .E6 K).subtype with hEdef
  have hEX : E ≤ xHat .E6 K modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hc hp)
  have hker : ∀ p ∈ P', κ p = 1 → p = 1 := fun p hp h1 =>
    eq_one_of_hatAut_eq_one (xHat_le_monoHat _ (hEX ⟨p, hp, rfl⟩)) h1
  have hP'X : P'.map κ = X.map (MulAut.conj (κ c)).toMonoidHom := by
    have hcomp : κ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (κ c)).toMonoidHom.comp κ :=
      MonoidHom.ext fun p => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    rw [hP', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPX]
  have hcardP' : Nat.card P' = Nat.card X := by
    rw [← card_map_eq_of_ker κ hker, hP'X,
      Subgroup.card_map_of_injective (MulAut.conj (κ c)).injective]
  have hcardE : Nat.card E = Nat.card X := by
    rw [hEdef, Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective, hcardP']
  have hXc : IsElemAbelian 3 (X.map (MulAut.conj (κ c)).toMonoidHom) :=
    TableB.isElemAbelian_map hX _
  have hP'ab : ∀ p ∈ P', ∀ p' ∈ P', p * p' = p' * p := by
    intro p hp p' hp'
    have h1 : κ (p * p' * (p' * p)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        TableB.IsElemAbelian.comm hXc (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
          (hP'X ▸ ⟨p', hp', rfl⟩ : κ p' ∈ _), mul_inv_cancel]
    have h2 := hker _ (mul_mem (mul_mem hp hp') (inv_mem (mul_mem hp' hp))) h1
    exact mul_inv_eq_one.mp h2
  have hP'3 : ∀ p ∈ P', p ^ 3 = 1 := by
    intro p hp
    refine hker _ (pow_mem hp 3) ?_
    rw [map_pow]
    exact hXc.2 _ (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
  have hP'el : IsElemAbelian 3 P' :=
    ⟨⟨⟨fun a b => Subtype.ext (hP'ab a a.2 b b.2)⟩⟩, hP'3⟩
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map hP'el _
  have : Finite E := Finite.of_surjective (fun p : P' => (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : E))
    (by rintro ⟨_, ⟨p, hp, rfl⟩⟩; exact ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨A, hAS, hA, hfixA, hcount, hbotA⟩ :=
    card_le_mul_card_diagKernel_of_le_xHat (τ := .E6) (p := 3) hζo hζ hE hEX
  have hiff : ∀ x : Fin Tag.E6.rank → ZMod 3,
      (diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj (κ c)).toMonoidHom) ↔
        rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ E := by
    intro x
    rw [← hP'X]
    constructor
    · rintro ⟨p, hp, hpκ⟩
      set d : hatGroup .E6 K :=
        ⟨rootDiagUnit .E6 (zetaVec ζ hζ x), rootDiagUnit_mem_hatGroup _⟩ with hd
      set q : hatGroup .E6 K := p * d⁻¹ with hq
      have hpE : (p : ModGL .E6 K) ∈ E := by
        rw [hEdef]
        exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      have hpM : (p : ModGL .E6 K) ∈ monoHat .E6 K :=
        xHat_le_monoHat _ (hEX hpE)
      have hqM : (q : ModGL .E6 K) ∈ monoHat .E6 K := by
        change (p : ModGL .E6 K) * (rootDiagUnit .E6 (zetaVec ζ hζ x))⁻¹ ∈ monoHat .E6 K
        exact mul_mem hpM (inv_mem (rootDiagUnit_mem_monoHat _))
      have hdκ : κ d = diag3 ζ hζ (Multiplicative.ofAdd x) := by
        change κ ⟨rootDiagUnit .E6 (zetaVec ζ hζ x), rootDiagUnit_mem_hatGroup _⟩ =
          diag3 ζ hζ (Multiplicative.ofAdd x)
        rw [hκrd (zetaVec ζ hζ x)]
        rfl
      have hqκ : κ q = 1 := by
        change κ (p * ⟨rootDiagUnit .E6 (zetaVec ζ hζ x), rootDiagUnit_mem_hatGroup _⟩⁻¹) = 1
        rw [map_mul, map_inv, hpκ, hdκ, mul_inv_cancel]
      have hq1 : q = 1 := by
        rw [hκ] at hqκ
        exact eq_one_of_hatAut_eq_one hqM hqκ
      have hpd_hat : p = d := mul_inv_eq_one.mp (hq ▸ hq1)
      have hpd : (p : ModGL .E6 K) = rootDiagUnit .E6 (zetaVec ζ hζ x) := by
        rw [hpd_hat]
      exact ⟨p, hp, hpd⟩
    · intro hy
      rw [hEdef] at hy
      obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hy
      refine ⟨p, hp, ?_⟩
      have hp' : p = ⟨rootDiagUnit .E6 (zetaVec ζ hζ x), rootDiagUnit_mem_hatGroup _⟩ :=
        Subtype.ext hp_eq
      rw [hp', hκrd (zetaVec ζ hζ x)]
      rfl
  have hcardset :
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        diag3 ζ hζ (Multiplicative.ofAdd x) ∈ X.map (MulAut.conj (κ c)).toMonoidHom} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ E} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hiff x)
  refine ⟨κ c, ⟨c, by rw [hκ]⟩, A, hA, ?_, ?_, ?_⟩
  · intro a ha x hx
    exact hfixA a ha x ((hiff x).mp hx)
  · rw [← hcardE, hcardset]
    exact hcount
  · intro hbot φ hφ
    rw [← hP'X] at hφ
    obtain ⟨p, hp, hpκ⟩ := hφ
    have hpE : (p : ModGL .E6 K) ∈ E := by
      rw [hEdef]
      exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨x, hx⟩ := hbotA hbot (p : ModGL .E6 K) hpE
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    have hp' : p = ⟨rootDiagUnit .E6 (zetaVec ζ hζ x), rootDiagUnit_mem_hatGroup _⟩ :=
      Subtype.ext hx
    have hpκ' : κ p = diag3 ζ hζ (Multiplicative.ofAdd x) := by
      rw [hp', hκrd (zetaVec ζ hζ x)]
      rfl
    rw [← hpκ, hpκ']

end Conj

end NoOffE6Three

end CFSG.StandardType
