module

public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofCore
import CFSG.Quasithin.Vol2.Ch1Fitting

public section

namespace CFSG.RankThree.PartTwo.Sec13.L3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped commutatorElement

section Aut

variable {Y : Type} [Group Y] {x₁ x₂ : Y}

theorem mulAut_ext_of_gen (h12 : x₁ * x₂ = x₂ * x₁)
    {σ τ : MulAut (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Y)}
    (h₁ : σ ⟨x₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)⟩ =
      τ ⟨x₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)⟩)
    (h₂ : σ ⟨x₂, Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)⟩ =
      τ ⟨x₂, Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)⟩) : σ = τ := by
  ext ⟨y, hy⟩
  obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hy
  have e : (⟨x₁ ^ i * x₂ ^ j, hy⟩ : (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Y)) =
      (⟨x₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)⟩ ^ i *
        ⟨x₂, Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)⟩ ^ j) := Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_zpow, h₁, h₂]

end Aut

section Involution

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_involution_of_q8 {x₁ x₂ n₁ n₂ : Y} (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (hN1 : n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹) (hN2 : n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁)
    (hZ : ∀ S : Subgroup Y, IsPGroup 2 S → ∀ k ∈ S, k * x₁ = x₁ * k → k * x₂ = x₂ * k →
      ∀ s ∈ S, k * s = s * k) :
    ∃ t : Y, t * t = 1 ∧ t * x₁ * t⁻¹ = x₁⁻¹ ∧ t * x₂ * t⁻¹ = x₂⁻¹ := by
  classical
  set E : Subgroup Y := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hEdef
  obtain ⟨hEc, hE3⟩ := sup_zpowers_facts h12 h1 h2
  have hx₁E : x₁ ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂E : x₂ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hconjE : ∀ n : Y, n * x₁ * n⁻¹ ∈ E → n * x₂ * n⁻¹ ∈ E →
      n ∈ Subgroup.normalizer (E : Set Y) := by
    intro n hn1 hn2
    refine mem_normalizer_of_conj_mem_of_finite fun y hy => ?_
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hy
    rw [show n * (x₁ ^ i * x₂ ^ j) * n⁻¹ = (n * x₁ * n⁻¹) ^ i * (n * x₂ * n⁻¹) ^ j by
      rw [conj_zpow, conj_zpow]; group]
    exact E.mul_mem (E.zpow_mem hn1 i) (E.zpow_mem hn2 j)
  have hn₁ : n₁ ∈ Subgroup.normalizer (E : Set Y) :=
    hconjE n₁ (by rw [hF1]; exact E.inv_mem hx₂E) (by rw [hF2]; exact hx₁E)
  have hn₂ : n₂ ∈ Subgroup.normalizer (E : Set Y) :=
    hconjE n₂ (by rw [hN1]; exact E.mul_mem (E.inv_mem hx₂E) (E.inv_mem hx₁E))
      (by rw [hN2]; exact E.mul_mem (E.mul_mem hx₁E hx₂E) hx₁E)
  set N : Subgroup Y := Subgroup.normalizer (E : Set Y) with hN
  set ρ : N →* MulAut E := E.normalizerMonoidHom with hρ
  have hρapp : ∀ (g : N) (y : E), ((ρ g y : E) : Y) = g * y * (g : Y)⁻¹ := fun g y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E g y
  set e₁ : E := ⟨x₁, hx₁E⟩
  set e₂ : E := ⟨x₂, hx₂E⟩
  set α := ρ ⟨n₁, hn₁⟩ with hα
  set β := ρ ⟨n₂, hn₂⟩ with hβ
  have hcommE : ∀ u v : E, u * v = v * u := fun u v =>
    Subtype.ext (mul_comm_of_mem hEc u.2 v.2)
  have hα1 : α e₁ = e₂⁻¹ := Subtype.ext (by rw [hρapp]; exact hF1)
  have hα2 : α e₂ = e₁ := Subtype.ext (by rw [hρapp]; exact hF2)
  have hβ1 : β e₁ = e₂⁻¹ * e₁⁻¹ := Subtype.ext (by rw [hρapp]; exact hN1)
  have hβ2 : β e₂ = e₁ * e₂ * e₁ := Subtype.ext (by rw [hρapp]; exact hN2)
  have he₁3 : e₁ ^ 3 = 1 := Subtype.ext (by simpa using h1)
  have he₂3 : e₂ ^ 3 = 1 := Subtype.ext (by simpa using h2)
  have hext : ∀ σ τ : MulAut E, σ e₁ = τ e₁ → σ e₂ = τ e₂ → σ = τ := fun σ τ h₁ h₂ =>
    mulAut_ext_of_gen h12 h₁ h₂
  have hαα1 : (α * α) e₁ = e₁⁻¹ := by
    rw [MulAut.mul_apply, hα1, map_inv, hα2]
  have hαα2 : (α * α) e₂ = e₂⁻¹ := by
    rw [MulAut.mul_apply, hα2, hα1]
  have hββ1 : (β * β) e₁ = e₁⁻¹ := by
    rw [MulAut.mul_apply, hβ1, map_mul, map_inv, map_inv, hβ1, hβ2]
    have := hcommE e₁ e₂
    calc (e₁ * e₂ * e₁)⁻¹ * (e₂⁻¹ * e₁⁻¹)⁻¹ = e₁⁻¹ * (e₂⁻¹ * (e₁⁻¹ * (e₁ * e₂))) := by group
      _ = e₁⁻¹ := by group
  have hββ2 : (β * β) e₂ = e₂⁻¹ := by
    rw [MulAut.mul_apply, hβ2, map_mul, map_mul, hβ1, hβ2]
    have h' : e₂⁻¹ * e₁⁻¹ * (e₁ * e₂ * e₁) * (e₂⁻¹ * e₁⁻¹) =
        e₂⁻¹ * (e₁⁻¹ * e₁) * (e₂ * e₁ * e₂⁻¹) * e₁⁻¹ := by group
    rw [h']
    have h'' : e₂ * e₁ * e₂⁻¹ = e₁ := by rw [← hcommE e₁ e₂]; group
    rw [h'']
    group
  have hαβ : α * α = β * β := hext _ _ (by rw [hαα1, hββ1]) (by rw [hαα2, hββ2])
  have hα4 : α * α * (α * α) = 1 := hext _ _
    (by rw [MulAut.mul_apply, hαα1, map_inv, hαα1, inv_inv, MulAut.one_apply])
    (by rw [MulAut.mul_apply, hαα2, map_inv, hαα2, inv_inv, MulAut.one_apply])
  have hx₁₁ : x₁ * x₁ = x₁⁻¹ := by
    rw [← sq]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h1])
  have hx₂₂ : x₂ * x₂ = x₂⁻¹ := by
    rw [← sq]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h2])
  have hαβα : α * β * α = β := by
    refine hext _ _ (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [MulAut.mul_apply, MulAut.mul_apply, hα1, map_inv, hβ2, map_inv, map_mul, map_mul,
        hα1, hα2, hβ1]
      simp only [Subgroup.coe_inv, Subgroup.coe_mul]
      calc (x₂⁻¹ * x₁ * x₂⁻¹)⁻¹ = x₂ * x₁⁻¹ * x₂ := by group
        _ = x₁⁻¹ * (x₁ * x₂) * x₁⁻¹ * x₂ := by group
        _ = x₁⁻¹ * (x₂ * x₁) * x₁⁻¹ * x₂ := by rw [h12]
        _ = x₁⁻¹ * (x₂ * x₂) := by group
        _ = x₁⁻¹ * x₂⁻¹ := by rw [hx₂₂]
        _ = (x₂ * x₁)⁻¹ := by group
        _ = (x₁ * x₂)⁻¹ := by rw [h12]
        _ = x₂⁻¹ * x₁⁻¹ := by group
    · rw [MulAut.mul_apply, MulAut.mul_apply, hα2, hβ1, map_mul, map_inv, map_inv, hα1, hα2,
        hβ2]
      simp only [Subgroup.coe_inv, Subgroup.coe_mul]
      calc x₁⁻¹ * x₂⁻¹⁻¹ = x₁⁻¹ * x₂ := by group
        _ = x₁ * x₁ * x₂ := by rw [hx₁₁]
        _ = x₁ * (x₁ * x₂) := by group
        _ = x₁ * (x₂ * x₁) := by rw [h12]
        _ = x₁ * x₂ * x₁ := by group
  have hcomm_ab : ⁅α, β⁆ = α * α := by
    rw [commutatorElement_def]
    calc α * β * α⁻¹ * β⁻¹ = α * β * (β * α)⁻¹ := by group
      _ = α * (α * β * α) * (β * α)⁻¹ := by rw [hαβα]
      _ = α * α := by group
  have hβαβ : β * α * β⁻¹ = α⁻¹ := by
    calc β * α * β⁻¹ = α⁻¹ * (α * β * α) * β⁻¹ := by group
      _ = α⁻¹ := by rw [hαβα]; group
  have hβN : β ∈ Subgroup.normalizer ((Subgroup.zpowers α : Subgroup (MulAut E)) :
      Set (MulAut E)) := by
    refine mem_normalizer_of_conj_mem_of_finite fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hβαβ]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers α)) k
  have h2grp : ∀ γ : MulAut E, γ * γ * (γ * γ) = 1 → IsPGroup 2 (Subgroup.zpowers γ) := by
    intro γ hγ
    have hγ4 : γ ^ (2 ^ 2) = 1 := by
      rw [show (2 ^ 2 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      exact hγ
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hγ4)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hβ4 : β * β * (β * β) = 1 := by rw [← hαβ, hα4]
  set Q : Subgroup (MulAut E) := Subgroup.zpowers α ⊔ Subgroup.zpowers β with hQ
  have hQ2 : IsPGroup 2 Q := IsPGroup.to_sup_of_normal_left' (h2grp α hα4) (h2grp β hβ4)
    (Subgroup.zpowers_le.mpr hβN)
  set H : Subgroup N := Q.comap ρ with hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  set ψ : H →* Q := (ρ.comp H.subtype).codRestrict Q (fun h => h.2) with hψ
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    have hQr : Q ≤ ρ.range := sup_le
      (Subgroup.zpowers_le.mpr ⟨⟨n₁, hn₁⟩, rfl⟩) (Subgroup.zpowers_le.mpr ⟨⟨n₂, hn₂⟩, rfl⟩)
    obtain ⟨m, hm⟩ := hQr hq
    refine ⟨⟨m, show ρ m ∈ Q from hm ▸ hq⟩, Subtype.ext ?_⟩
    exact hm
  have hQtop : IsPGroup 2 (⊤ : Subgroup Q) := hQ2.of_equiv Subgroup.topEquiv.symm
  have htop := ((S.mapSurjective hψsurj).is_maximal' hQtop le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  have hlift : ∀ q ∈ Q, ∃ s ∈ (S : Subgroup H), ρ (s : N) = q := by
    intro q hq
    have hmem : (⟨q, hq⟩ : Q) ∈ (S : Subgroup H).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hsq⟩ := hmem
    exact ⟨s, hs, congrArg Subtype.val hsq⟩
  obtain ⟨a, haS, hρa⟩ := hlift α (Subgroup.mem_sup_left (Subgroup.mem_zpowers α))
  obtain ⟨b, hbS, hρb⟩ := hlift β (Subgroup.mem_sup_right (Subgroup.mem_zpowers β))
  set SY : Subgroup Y := ((S : Subgroup H).map H.subtype).map N.subtype with hSY
  have hSY2 : IsPGroup 2 SY := (S.isPGroup'.map _).map _
  have hmemSY : ∀ s ∈ (S : Subgroup H), (((s : H) : N) : Y) ∈ SY := fun s hs =>
    ⟨(s : N), ⟨s, hs, rfl⟩, rfl⟩
  set A : Y := (((a : H) : N) : Y) with hA
  set B : Y := (((b : H) : N) : Y) with hB
  set c : Y := ⁅A, B⁆ with hc
  have hASY : A ∈ SY := hmemSY a haS
  have hBSY : B ∈ SY := hmemSY b hbS
  have hcSY : c ∈ SY := by
    rw [hc, commutatorElement_def]
    exact SY.mul_mem (SY.mul_mem (SY.mul_mem hASY hBSY) (SY.inv_mem hASY)) (SY.inv_mem hBSY)
  set cN : N := ⁅((a : H) : N), ((b : H) : N)⁆ with hcN
  have hcNY : (cN : Y) = c := by
    simp only [hcN, hc, hA, hB, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have hρc : ρ cN = α * α := by
    rw [hcN, map_commutatorElement, hρa, hρb, hcomm_ab]
  have hcx₁ : c * x₁ * c⁻¹ = x₁⁻¹ := by
    have h := congrArg (fun σ : MulAut E => ((σ e₁ : E) : Y)) hρc
    rw [hρapp, hαα1, hcNY] at h
    simpa using h
  have hcx₂ : c * x₂ * c⁻¹ = x₂⁻¹ := by
    have h := congrArg (fun σ : MulAut E => ((σ e₂ : E) : Y)) hρc
    rw [hρapp, hαα2, hcNY] at h
    simpa using h
  have hcentr : ∀ g : N, ρ g = 1 → (g : Y) * x₁ = x₁ * g ∧ (g : Y) * x₂ = x₂ * g := by
    intro g hg
    have h₁ := congrArg (fun σ : MulAut E => ((σ e₁ : E) : Y)) hg
    have h₂ := congrArg (fun σ : MulAut E => ((σ e₂ : E) : Y)) hg
    simp only [hρapp, MulAut.one_apply] at h₁ h₂
    refine ⟨?_, ?_⟩
    · calc (g : Y) * x₁ = (g : Y) * x₁ * (g : Y)⁻¹ * g := by group
        _ = x₁ * g := by rw [h₁]
    · calc (g : Y) * x₂ = (g : Y) * x₂ * (g : Y)⁻¹ * g := by group
        _ = x₂ * g := by rw [h₂]
  have hk₁ : ρ (cN⁻¹ * (((a : H) : N) * ((a : H) : N))) = 1 := by
    rw [map_mul, map_inv, map_mul, hρc, hρa, inv_mul_cancel]
  have hk₂ : ρ (cN⁻¹ * (((b : H) : N) * ((b : H) : N))) = 1 := by
    rw [map_mul, map_inv, map_mul, hρc, hρb, hαβ, inv_mul_cancel]
  have hk₁Y : ((cN⁻¹ * (((a : H) : N) * ((a : H) : N)) : N) : Y) = c⁻¹ * (A * A) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hcNY]
  have hk₂Y : ((cN⁻¹ * (((b : H) : N) * ((b : H) : N)) : N) : Y) = c⁻¹ * (B * B) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hcNY]
  obtain ⟨hk₁x₁, hk₁x₂⟩ := hcentr _ hk₁
  obtain ⟨hk₂x₁, hk₂x₂⟩ := hcentr _ hk₂
  rw [hk₁Y] at hk₁x₁ hk₁x₂
  rw [hk₂Y] at hk₂x₁ hk₂x₂
  set k₁ := c⁻¹ * (A * A) with hk₁def
  set k₂ := c⁻¹ * (B * B) with hk₂def
  have hk₁S : k₁ ∈ SY := SY.mul_mem (SY.inv_mem hcSY) (SY.mul_mem hASY hASY)
  have hk₂S : k₂ ∈ SY := SY.mul_mem (SY.inv_mem hcSY) (SY.mul_mem hBSY hBSY)
  have hz₁ := hZ SY hSY2 _ hk₁S hk₁x₁ hk₁x₂
  have hz₂ := hZ SY hSY2 _ hk₂S hk₂x₁ hk₂x₂
  have hAk₁ : Commute A k₁ := (show Commute k₁ A from hz₁ A hASY).symm
  have hBk₂ : Commute B k₂ := (show Commute k₂ B from hz₂ B hBSY).symm
  have hAk₂ : Commute A k₂ := (show Commute k₂ A from hz₂ A hASY).symm
  have hcA1 : c = A * A * k₁⁻¹ := by rw [hk₁def]; group
  have hcB1 : c = B * B * k₂⁻¹ := by rw [hk₂def]; group
  have hcA : Commute A c := by
    rw [hcA1]
    exact ((Commute.refl A).mul_right (Commute.refl A)).mul_right hAk₁.inv_right
  have hcB : Commute B c := by
    rw [hcB1]
    exact ((Commute.refl B).mul_right (Commute.refl B)).mul_right hBk₂.inv_right
  have hcc : c * c = 1 := by
    have hBB : B * B = c * k₂ := by rw [hk₂def]; group
    have hAB2 : A * (B * B) * A⁻¹ = B * B := by
      have hc' : Commute A (c * k₂) := hcA.mul_right hAk₂
      rw [hBB, hc'.eq]
      group
    have hABA : A * B * A⁻¹ = c * B := by rw [hc, commutatorElement_def]; group
    have hsq : (A * B * A⁻¹) * (A * B * A⁻¹) = A * (B * B) * A⁻¹ := by group
    rw [hABA, hAB2] at hsq
    have h4 : c * B * (c * B) = c * c * (B * B) := by
      calc c * B * (c * B) = c * (B * c) * B := by group
        _ = c * (c * B) * B := by rw [hcB.eq]
        _ = c * c * (B * B) := by group
    rw [h4] at hsq
    calc c * c = c * c * (B * B) * (B * B)⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  exact ⟨c, hcc, hcx₁, hcx₂⟩

end Involution

theorem mem_normalizer_sup_of_conj {Y : Type} [Group Y] [Finite Y] {x₁ x₂ n : Y}
    (h12 : x₁ * x₂ = x₂ * x₁)
    (hn1 : n * x₁ * n⁻¹ ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Y))
    (hn2 : n * x₂ * n⁻¹ ∈ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Y)) :
    n ∈ Subgroup.normalizer
      ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup Y) : Set Y) := by
  refine mem_normalizer_of_conj_mem_of_finite fun y hy => ?_
  obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hy
  rw [show n * (x₁ ^ i * x₂ ^ j) * n⁻¹ = (n * x₁ * n⁻¹) ^ i * (n * x₂ * n⁻¹) ^ j by
    rw [conj_zpow, conj_zpow]; group]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hn1 i) (Subgroup.zpow_mem _ hn2 j)

theorem exists_pCore_not_commute {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K)
    (hq : ¬ IsQuasisimple X) {x : X} (hx : x ∉ K) :
    ∃ s : ℕ, s.Prime ∧ ∃ y ∈ CFSG.pCore s X, y * x ≠ x * y := by
  by_contra hcon
  push Not at hcon
  have hnt : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx (Subsingleton.elim x 1 ▸ K.one_mem)
  have hns : ¬ Group.IsSolvable X := Group.IsPerfect.not_isSolvable X
  have hmax : ∀ P : Subgroup X, P.Normal → P = ⊤ ∨ Group.IsSolvable P := by
    intro P hP
    by_cases hPK : P ≤ K
    · right
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPK)
    · left
      exact Sec4.Census.eq_top_of_not_le hK hPK
  have hCF := CFSG.Quasithin.centralizer_fittingSubgroup_le_of_not_isQuasisimple
    (inferInstance : Group.IsPerfect X) hmax hns hq
  have hxC : x ∈ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) :=
    CFSG.Quasithin.mem_centralizer_fittingSubgroup_of_centralizes_pCores fun s hs y hy =>
      hcon s hs y hy
  have hFK : CFSG.fittingSubgroup X ≤ K :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance inferInstance
  exact hx (hFK (hCF hxC))

end CFSG.RankThree.PartTwo.Sec13.L3Proof
