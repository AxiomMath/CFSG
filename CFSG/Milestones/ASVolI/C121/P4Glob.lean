module

public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.CGT.PushingUpLit.CGT6X.ExtCocycle

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped MatrixGroups Matrix

section Global

variable {𝕎 : Type} [CommGroup 𝕎] [Finite 𝕎]

theorem burnsideC121_p4_centQuot_normal {G : Subgroup (MulAut 𝕎)} {U : Subgroup 𝕎}
    (hG : G ≤ stabSub U) : ∀ g ∈ G, ∀ x ∈ G ⊓ centQuot U, g * x * g⁻¹ ∈ G ⊓ centQuot U := by
  intro g hg x hx
  refine ⟨G.mul_mem (G.mul_mem hg hx.1) (G.inv_mem hg), fun v => ?_⟩
  have h1 : x (g⁻¹ v) * (g⁻¹ v)⁻¹ ∈ U := hx.2 (g⁻¹ v)
  have h2 : g (x (g⁻¹ v) * (g⁻¹ v)⁻¹) ∈ U := ((hG hg) _).2 h1
  have h3 : (g * x * g⁻¹) v * v⁻¹ = g (x (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
    rw [map_mul, map_inv]
    have : g (g⁻¹ v) = v := by simp
    rw [this]
    rfl
  rw [h3]
  exact h2

theorem burnsideC121_p4_centSub_normal {G : Subgroup (MulAut 𝕎)} {U : Subgroup 𝕎}
    (hG : G ≤ stabSub U) : ∀ g ∈ G, ∀ x ∈ G ⊓ centSub U, g * x * g⁻¹ ∈ G ⊓ centSub U := by
  intro g hg x hx
  refine ⟨G.mul_mem (G.mul_mem hg hx.1) (G.inv_mem hg), fun u hu => ?_⟩
  have h1 : g⁻¹ u ∈ U := ((hG (G.inv_mem hg)) u).2 hu
  have h2 : x (g⁻¹ u) = g⁻¹ u := hx.2 _ h1
  show g (x (g⁻¹ u)) = u
  rw [h2]
  simp

theorem burnsideC121_p4_eq_zero_of_fixed_all {F : Type} [Field F] (v : Fin 2 → F)
    (h : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : v = 0 := by
  let t₁ : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let t₂ : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have h1 := congrFun (h t₁) 0
  have h2 := congrFun (h t₂) 1
  simp [t₁, t₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  funext i
  fin_cases i
  · simpa using h2
  · simpa using h1

theorem burnsideC121_p4_global_of_section (h2 : ∀ w : 𝕎, w ^ 2 = 1)
    {G : Subgroup (MulAut 𝕎)} {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (θ : ↥G ≃* SL(2, F)) {U₁ U₂ : Subgroup 𝕎} (hU : U₂ ≤ U₁)
    (hG₁ : G ≤ stabSub U₁) (hG₂ : G ≤ stabSub U₂)
    (e : Sec U₁ U₂ ≃* Multiplicative (Fin 2 → F))
    (he : ∀ (g : ↥G) (x : Sec U₁ U₂), e (B5.secHom G hG₁ hG₂ g x) =
      Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (e x)))
    {A : Subgroup (MulAut 𝕎)} (hAG : A ≤ G) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hFF : Nat.card 𝕎 ≤ Nat.card A * Nat.card (fixV A))
    (hnorm : ∀ N : Subgroup (MulAut 𝕎), N ≤ G → (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      A ≤ N → N = G) :
    ∃ β : 𝕎 →* Multiplicative (Fin 2 → F), Function.Surjective β ∧ β.ker = fixV G ∧
      ∀ (g : ↥G) (w : 𝕎), β ((g : MulAut 𝕎) w) =
        Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β w)) := by
  classical
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  set q : ℕ := 2 ^ n with hq
  have hqpos : 0 < q := by positivity
  have hGc : Nat.card G = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr θ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFc]
  obtain ⟨hAq, hAidx⟩ := B42L2.card_le_of_isPGroup hAG hAe.isPGroup hn hGc
  have hAU₁ : A ≤ stabSub U₁ := hAG.trans hG₁
  have hMc : Nat.card (Sec U₁ U₂) = q * q := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fin, hFc, sq]
  have hCM : Nat.card (fixV (autSec A U₁ U₂)) ≤ q := by
    obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    set M : Matrix (Fin 2) (Fin 2) F := (θ ⟨a, hAG haA⟩ : Matrix (Fin 2) (Fin 2) F) with hMdef
    have hM : M ≠ 1 := by
      intro h
      have h1 : θ ⟨a, hAG haA⟩ = 1 := Subtype.ext h
      have h2 : (⟨a, hAG haA⟩ : ↥G) = 1 := θ.injective (h1.trans (map_one θ).symm)
      exact ha1' (congrArg Subtype.val h2)
    have hmem : B5.secHom G hG₁ hG₂ ⟨a, hAG haA⟩ ∈ autSec A U₁ U₂ := by
      rw [← B5.map_secHom_eq_autSec G hG₁ hG₂ hAG]
      exact ⟨⟨a, hAG haA⟩, haA, rfl⟩
    let f : ↥(fixV (autSec A U₁ U₂)) → {x : Fin 2 → F // M.mulVec x = x} := fun x =>
      ⟨Multiplicative.toAdd (e x), by
        have h1 := he ⟨a, hAG haA⟩ x
        rw [show B5.secHom G hG₁ hG₂ ⟨a, hAG haA⟩ (x : Sec U₁ U₂) = x from x.2 _ hmem] at h1
        exact (congrArg Multiplicative.toAdd h1).symm⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : e x = e y := Multiplicative.toAdd.injective (congrArg Subtype.val hxy)
      exact Subtype.ext (e.injective h1)
    calc Nat.card (fixV (autSec A U₁ U₂)) ≤ Nat.card {x : Fin 2 → F // M.mulVec x = x} :=
          Nat.card_le_card_of_injective f hf
      _ ≤ Nat.card F := B42L2.card_fixed_le M hM
      _ = q := hFc
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ fixV A, a * b = b * a := fun a _ b _ => mul_comm a b
  have hsup := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf := card_inf_fixV_le_autSec hU hAU₁
  have hsec := card_sec_mul hU
  have hsupW : Nat.card ↥(U₁ ⊔ fixV A) ≤ Nat.card 𝕎 := Subgroup.card_le_card_group _
  have hinf2 : Nat.card ↥(U₂ ⊓ fixV A) ≤ Nat.card U₂ := Subgroup.card_le_of_le inf_le_left
  have hU2pos : 0 < Nat.card U₂ := Nat.card_pos
  have hcpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have hi1pos : 0 < Nat.card ↥(U₁ ⊓ fixV A) := Nat.card_pos
  have hcmpos : 0 < Nat.card (fixV (autSec A U₁ U₂)) := Nat.card_pos
  have hWpos : 0 < Nat.card 𝕎 := Nat.card_pos
  set s := Nat.card (Sec U₁ U₂)
  set u₂ := Nat.card U₂
  set c := Nat.card (fixV A)
  set w := Nat.card 𝕎
  set j := Nat.card ↥(U₁ ⊔ fixV A)
  set i₁ := Nat.card ↥(U₁ ⊓ fixV A)
  set cm := Nat.card (fixV (autSec A U₁ U₂))
  set i₂ := Nat.card ↥(U₂ ⊓ fixV A)
  set a := Nat.card A
  have e1 : s * u₂ * c = j * i₁ := by rw [hsec, hsup]
  have c1 : j * i₁ ≤ w * i₁ := Nat.mul_le_mul_right _ hsupW
  have c2 : w * i₁ ≤ w * (cm * i₂) := Nat.mul_le_mul_left _ hinf
  have c3 : w * (cm * i₂) ≤ w * (cm * u₂) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinf2)
  have c4 : w * (cm * u₂) ≤ (a * c) * (cm * u₂) := Nat.mul_le_mul_right _ hFF
  have c5 : (a * c) * (cm * u₂) ≤ (q * c) * (q * u₂) := by
    calc (a * c) * (cm * u₂) = (a * cm) * (c * u₂) := by ring
      _ ≤ (q * q) * (c * u₂) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hAq hCM)
      _ = (q * c) * (q * u₂) := by ring
  have e2 : (q * c) * (q * u₂) = s * u₂ * c := by rw [hMc]; ring
  have hj : j = w := by
    have : j * i₁ = w * i₁ := le_antisymm c1 (by omega)
    exact Nat.eq_of_mul_eq_mul_right hi1pos this
  have hi2 : i₂ = u₂ := by
    have h1 : w * (cm * i₂) = w * (cm * u₂) := le_antisymm c3 (by omega)
    have h2 : cm * i₂ = cm * u₂ := Nat.eq_of_mul_eq_mul_left hWpos h1
    exact Nat.eq_of_mul_eq_mul_left hcmpos h2
  have haq : a = q := by
    have h1 : (a * c) * (cm * u₂) = (q * c) * (q * u₂) := le_antisymm c5 (by omega)
    have h2 : (a * cm) * (c * u₂) = (q * q) * (c * u₂) := by
      calc (a * cm) * (c * u₂) = (a * c) * (cm * u₂) := by ring
        _ = (q * c) * (q * u₂) := h1
        _ = (q * q) * (c * u₂) := by ring
    have h3 : a * cm = q * q := Nat.eq_of_mul_eq_mul_right (by positivity) h2
    by_contra hne
    have hlt : a < q := lt_of_le_of_ne hAq hne
    have : a * cm < q * q := Nat.mul_lt_mul_of_lt_of_le hlt hCM hqpos
    omega
  have htopA : U₁ ⊔ fixV A = ⊤ := Subgroup.eq_top_of_card_eq _ hj
  have hU₂A : U₂ ≤ fixV A := by
    have : U₂ ⊓ fixV A = U₂ := Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hi2.symm)
    rw [← this]
    exact inf_le_right
  have hGq : G ≤ centQuot U₁ := by
    have hN := hnorm (G ⊓ centQuot U₁) inf_le_left (burnsideC121_p4_centQuot_normal hG₁) (by
      intro x hx
      refine ⟨hAG hx, fun v => ?_⟩
      obtain ⟨u, hu, d, hd, rfl⟩ := Subgroup.mem_sup.1 (htopA ▸ Subgroup.mem_top v)
      have hd' : x d = d := hd x hx
      have hxu : x u ∈ U₁ := ((hAU₁ hx) u).2 hu
      have : x (u * d) * (u * d)⁻¹ = x u * u⁻¹ := by
        rw [map_mul, hd', mul_inv_rev]
        group
      rw [this]
      exact U₁.mul_mem hxu (U₁.inv_mem hu))
    rw [← hN]
    exact inf_le_right
  have hGc₂ : G ≤ centSub U₂ := by
    have hN := hnorm (G ⊓ centSub U₂) inf_le_left (burnsideC121_p4_centSub_normal hG₂)
      (fun x hx => ⟨hAG hx, fun u hu => hU₂A hu x hx⟩)
    rw [← hN]
    exact inf_le_right
  have hodd : Odd (A.subgroupOf G).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (hAidx haq))
  have hfixA : fixV A ≤ U₁ ⊔ fixV G := by
    intro x hx
    let ρ : ↥G →* MulAut ↥U₁ := (resHom U₁).comp (Subgroup.inclusion hG₁)
    have hρ : ∀ (g : ↥G) (u : ↥U₁), ((ρ g u : ↥U₁) : 𝕎) = (g : MulAut 𝕎) u := fun g u => rfl
    let f : ↥G → ↥U₁ := fun g => ⟨(g : MulAut 𝕎) x * x⁻¹, hGq g.2 x⟩
    have hf : CFSG.CGT.PushingUpLit.CGT6X.IsCocycle ρ f := by
      intro g h
      apply Subtype.ext
      simp only [f, Subgroup.coe_mul, hρ, MulAut.mul_apply, map_mul, map_inv]
      have : (g : MulAut 𝕎) ((h : MulAut 𝕎) x) * x⁻¹ =
          (g : MulAut 𝕎) x * x⁻¹ * ((g : MulAut 𝕎) ((h : MulAut 𝕎) x) *
            ((g : MulAut 𝕎) x)⁻¹) := by
        rw [mul_comm ((g : MulAut 𝕎) x * x⁻¹), mul_assoc, ← mul_assoc ((g : MulAut 𝕎) x)⁻¹,
          inv_mul_cancel, one_mul]
      exact this
    have hvan : ∀ h ∈ A.subgroupOf G, f h = 1 := by
      intro h hh
      apply Subtype.ext
      show (h : MulAut 𝕎) x * x⁻¹ = 1
      rw [hx (h : MulAut 𝕎) (Subgroup.mem_subgroupOf.1 hh), mul_inv_cancel]
    have h2U : ∀ v : ↥U₁, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using h2 v)
    obtain ⟨m, hm⟩ := CFSG.CGT.PushingUpLit.CGT6X.coboundary_of_vanish_on_odd_index h2U
      (A.subgroupOf G) hodd hf hvan
    have hxm : x * (m : 𝕎)⁻¹ ∈ fixV G := by
      intro g hg
      have h1 := congrArg Subtype.val (hm ⟨g, hg⟩)
      simp only [f, hρ, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [map_mul, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_div_eq_div,
        div_eq_mul_inv, div_eq_mul_inv]
      exact h1
    have : x = (m : 𝕎) * (x * (m : 𝕎)⁻¹) := by
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left m.2) (Subgroup.mem_sup_right hxm)
  have htop : U₁ ⊔ fixV G = ⊤ := by
    rw [eq_top_iff, ← htopA]
    exact sup_le le_sup_left hfixA
  have hU₁G : ∀ u : ↥U₁, (u : 𝕎) ∈ fixV G → (u : 𝕎) ∈ U₂ := by
    intro u hu
    have hfix : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (e (QuotientGroup.mk u)) = Multiplicative.toAdd (e (QuotientGroup.mk u)) := by
      intro g
      have h1 := he (θ.symm g) (QuotientGroup.mk u)
      rw [B5.secHom_mk] at h1
      have h3 : (⟨((θ.symm g : ↥G) : MulAut 𝕎) (u : 𝕎), (hG₁ (θ.symm g).2 u).2 u.2⟩ : ↥U₁) = u :=
        Subtype.ext (hu _ (θ.symm g).2)
      rw [h3, MulEquiv.apply_symm_apply] at h1
      exact (congrArg Multiplicative.toAdd h1).symm
    have h0 := burnsideC121_p4_eq_zero_of_fixed_all _ hfix
    have h1 : e (QuotientGroup.mk u) = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    have h2' : (QuotientGroup.mk u : Sec U₁ U₂) = 1 := by
      have := congrArg e.symm h1
      simpa using this
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2'
    exact h2'
  set C := fixV G with hC
  let π : ↥U₁ →* 𝕎 ⧸ C := (QuotientGroup.mk' C).comp U₁.subtype
  have hπs : Function.Surjective π := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H v =>
      obtain ⟨u, hu, d, hd, rfl⟩ := Subgroup.mem_sup.1 (htop ▸ Subgroup.mem_top v)
      refine ⟨⟨u, hu⟩, ?_⟩
      show (QuotientGroup.mk u : 𝕎 ⧸ C) = QuotientGroup.mk (u * d)
      rw [QuotientGroup.eq]
      simpa using C.inv_mem hd
  have hπk : U₂.subgroupOf U₁ = π.ker := by
    ext u
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, π, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.coe_subtype]
    exact ⟨fun hu g hg => hGc₂ hg _ hu, hU₁G u⟩
  let ψ : Sec U₁ U₂ ≃* 𝕎 ⧸ C :=
    (QuotientGroup.quotientMulEquivOfEq hπk).trans (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  have hψ : ∀ u : ↥U₁, ψ (QuotientGroup.mk u) = QuotientGroup.mk (u : 𝕎) := fun u => rfl
  let β : 𝕎 →* Multiplicative (Fin 2 → F) :=
    (e.toMonoidHom.comp ψ.symm.toMonoidHom).comp (QuotientGroup.mk' C)
  have hβu : ∀ u : ↥U₁, β u = e (QuotientGroup.mk u) := by
    intro u
    show e (ψ.symm (QuotientGroup.mk (u : 𝕎))) = _
    rw [← hψ, MulEquiv.symm_apply_apply]
  have hβker : β.ker = C := by
    ext v
    simp only [MonoidHom.mem_ker, β, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨β, ?_, hβker, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective C (ψ (e.symm y))
    refine ⟨v, ?_⟩
    show e (ψ.symm (QuotientGroup.mk' C v)) = _
    rw [hv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  · intro g v
    obtain ⟨u, hu, d, hd, rfl⟩ := Subgroup.mem_sup.1 (htop ▸ Subgroup.mem_top v)
    have hβd : β d = 1 := by rw [← MonoidHom.mem_ker, hβker]; exact hd
    have hgd : (g : MulAut 𝕎) d = d := hd g g.2
    have hgu : (g : MulAut 𝕎) u ∈ U₁ := ((hG₁ g.2) u).2 hu
    rw [map_mul, hgd, map_mul, map_mul, hβd, mul_one, mul_one]
    have k1 : β ((g : MulAut 𝕎) u) = e (QuotientGroup.mk ⟨(g : MulAut 𝕎) u, hgu⟩) :=
      hβu ⟨_, hgu⟩
    have k2 : β u = e (QuotientGroup.mk ⟨u, hu⟩) := hβu ⟨u, hu⟩
    rw [k1, k2, ← he g (QuotientGroup.mk ⟨u, hu⟩), B5.secHom_mk]

end Global

end CFSG.Quasithin
