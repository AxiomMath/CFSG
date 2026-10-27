module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.A1cModuleBridge

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] noncomputable def nB (B : Subgroup Γ) (S : Subgroup Q) : ℕ :=
  rk ↥S - rk ↥(S ⊓ XMod.fixed ↥B (⊤ : Subgroup Q))

theorem nB_mono [Finite Q] (B : Subgroup Γ) {S S' : Subgroup Q} (h : S ≤ S') : nB B S ≤ nB B S' := by
  unfold nB
  set F := XMod.fixed ↥B (⊤ : Subgroup Q) with hF
  have h1 := rk_sup_add_rk_inf S (S' ⊓ F)
  have h2 : S ⊔ S' ⊓ F ≤ S' := sup_le h inf_le_left
  have h3 := rk_mono h2
  have h4 : S ⊓ (S' ⊓ F) = S ⊓ F := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, h hx.1, hx.2⟩⟩
  rw [h4] at h1
  have h5 : rk ↥(S ⊓ F) ≤ rk ↥S := rk_mono inf_le_left
  have h6 : rk ↥(S' ⊓ F) ≤ rk ↥S' := rk_mono inf_le_left
  omega

theorem nB_sup_of_disjoint [Finite Q] (B : Subgroup Γ) {S S' : Subgroup Q} (hS : XMod.IsInv ↥B S)
    (hS' : XMod.IsInv ↥B S') (hd : S ⊓ S' = ⊥) : nB B (S ⊔ S') = nB B S + nB B S' := by
  unfold nB
  set F := XMod.fixed ↥B (⊤ : Subgroup Q) with hF
  have h1 := rk_sup_add_rk_inf S S'
  rw [hd, rk_bot] at h1
  have hE : (S ⊔ S') ⊓ F = S ⊓ F ⊔ S' ⊓ F := by
    refine le_antisymm ?_ (sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right))
    rintro x ⟨hx, hxF⟩
    obtain ⟨s, hs, s', hs', rfl⟩ := Subgroup.mem_sup.1 hx
    have hfix : ∀ b : ↥B, b • (s * s') = s * s' := fun b => (XMod.mem_fixed.1 hxF).2 b
    have hs_fix : ∀ b : ↥B, b • s = s := by
      intro b
      have h2 := hfix b
      rw [smul_mul'] at h2
      have h3 : (b • s) / s = s' / (b • s') := by
        rw [div_eq_div_iff_mul_eq_mul, h2, mul_comm]
      have h4 : (b • s) / s ∈ S ⊓ S' :=
        ⟨S.div_mem (hS b s hs) hs, by
          rw [h3]; exact S'.div_mem hs' (hS' b s' hs')⟩
      rw [hd, Subgroup.mem_bot, div_eq_one] at h4
      exact h4
    have hs'_fix : ∀ b : ↥B, b • s' = s' := by
      intro b
      have h2 := hfix b
      rw [smul_mul', hs_fix b] at h2
      exact mul_left_cancel h2
    exact Subgroup.mul_mem_sup ⟨hs, XMod.mem_fixed.2 ⟨trivial, hs_fix⟩⟩ ⟨hs', XMod.mem_fixed.2 ⟨trivial, hs'_fix⟩⟩
  have hd2 : (S ⊓ F) ⊓ (S' ⊓ F) = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hd]
    exact fun x hx => ⟨hx.1.1, hx.2.1⟩
  have h2 := rk_sup_add_rk_inf (S ⊓ F) (S' ⊓ F)
  rw [hd2, rk_bot] at h2
  rw [hE]
  have h5 : rk ↥(S ⊓ F) ≤ rk ↥S := rk_mono inf_le_left
  have h6 : rk ↥(S' ⊓ F) ≤ rk ↥S' := rk_mono inf_le_left
  omega

theorem mem_conjMap {B : Subgroup Γ} {g x : Γ} :
    x ∈ B.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ B := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    show g⁻¹ * (g * b * g⁻¹) * g ∈ B
    rw [show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    exact hb
  · intro h
    exact ⟨g⁻¹ * x * g, h, show g * (g⁻¹ * x * g) * g⁻¹ = x by group⟩

theorem rk_smul (g : Γ) (S : Subgroup Q) : rk ↥(g • S) = rk ↥S := by
  unfold rk
  rw [Nat.card_congr (XMod.smulEquiv g S).toEquiv.symm]

theorem fixed_conj (B : Subgroup Γ) (g : Γ) :
    XMod.fixed ↥(B.map (MulAut.conj g).toMonoidHom) (⊤ : Subgroup Q) =
      g • XMod.fixed ↥B (⊤ : Subgroup Q) := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [XMod.mem_fixed, Subgroup.mem_top, true_and]
  constructor
  · intro h b
    have hb : g * (b : Γ) * g⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom := by
      rw [mem_conjMap, show g⁻¹ * (g * (b : Γ) * g⁻¹) * g = b by group]
      exact b.2
    have h1 := h ⟨g * (b : Γ) * g⁻¹, hb⟩
    change (g * (b : Γ) * g⁻¹) • q = q at h1
    change (b : Γ) • g⁻¹ • q = g⁻¹ • q
    rw [mul_smul, mul_smul] at h1
    have h2 := congrArg (fun z => g⁻¹ • z) h1
    simpa [smul_smul] using h2
  · intro h b'
    have hb' := mem_conjMap.1 b'.2
    have h1 := h ⟨g⁻¹ * (b' : Γ) * g, hb'⟩
    change (g⁻¹ * (b' : Γ) * g) • g⁻¹ • q = g⁻¹ • q at h1
    change (b' : Γ) • q = q
    have h2 := congrArg (fun z => g • z) h1
    simp only [smul_smul] at h2
    simpa [mul_assoc] using h2

theorem nB_smul (B : Subgroup Γ) (g : Γ) (S : Subgroup Q) :
    nB (B.map (MulAut.conj g).toMonoidHom) (g • S) = nB B S := by
  unfold nB
  rw [fixed_conj, ← Subgroup.smul_inf, rk_smul, rk_smul]

@[expose] def QuotMod (N : Subgroup Q) (_hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) : Type _ := Q ⧸ N

instance quotModCommGroup (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    CommGroup (QuotMod N hN) :=
  inferInstanceAs (CommGroup (Q ⧸ N))

@[expose] def QuotMod.mk (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) : Q →* QuotMod N hN :=
  QuotientGroup.mk' N

theorem QuotMod.mk_surjective (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    Function.Surjective (QuotMod.mk N hN) :=
  QuotientGroup.mk'_surjective N

theorem QuotMod.ker_mk (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    (QuotMod.mk N hN).ker = N :=
  QuotientGroup.ker_mk' N

@[expose] noncomputable def quotModSMul (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) (g : Γ) :
    QuotMod N hN →* QuotMod N hN :=
  QuotientGroup.map N N (MulDistribMulAction.toMonoidHom Q g) (fun n hn => hN g n hn)

noncomputable instance quotModAct (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    MulDistribMulAction Γ (QuotMod N hN) where
  smul g q := quotModSMul N hN g q
  one_smul q := by
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective N hN q
    exact congrArg (QuotMod.mk N hN) (one_smul Γ x)
  mul_smul s t q := by
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective N hN q
    exact congrArg (QuotMod.mk N hN) (mul_smul s t x)
  smul_mul g p q := map_mul _ _ _
  smul_one g := map_one _

theorem quotMod_smul_mk (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) (g : Γ) (q : Q) :
    g • (QuotMod.mk N hN q) = QuotMod.mk N hN (g • q) := rfl

instance quotModFinite [Finite Q] (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    Finite (QuotMod N hN) :=
  inferInstanceAs (Finite (Q ⧸ N))

theorem rk_quotMod_top [Finite Q] (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    rk ↥(⊤ : Subgroup (QuotMod N hN)) = rkIdx N := by
  rw [rk_top]
  unfold rk rkIdx
  rfl

theorem nB_chain [Finite Q] (B : Subgroup Γ) (N : Subgroup Q) (hN : ∀ g : Γ, ∀ n ∈ N, g • n ∈ N) :
    nB B N + nB B (⊤ : Subgroup (QuotMod N hN)) ≤ nB B (⊤ : Subgroup Q) := by
  unfold nB
  set F := XMod.fixed ↥B (⊤ : Subgroup Q) with hF
  set F' := XMod.fixed ↥B (⊤ : Subgroup (QuotMod N hN)) with hF'
  have himg : F.map (QuotMod.mk N hN) ≤ F' := by
    rintro _ ⟨x, hx, rfl⟩
    refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
    have hb := (XMod.mem_fixed.1 hx).2 b
    change (b : Γ) • x = x at hb
    change (b : Γ) • (QuotMod.mk N hN x) = QuotMod.mk N hN x
    rw [quotMod_smul_mk, hb]
  have h1 := B1More.card_map_mul_card_inf_ker F (QuotMod.mk N hN)
  rw [QuotMod.ker_mk] at h1
  have h1' : rk ↥(F.map (QuotMod.mk N hN)) + rk ↥(F ⊓ N) = rk ↥F := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
  have h2 : rk ↥(F.map (QuotMod.mk N hN)) ≤ rk ↥F' := rk_mono himg
  have h3 := rk_add_rkIdx N
  have h4 := rk_quotMod_top N hN
  have h5 : rk ↥(N ⊓ F) ≤ rk ↥N := rk_mono inf_le_left
  have h6 : rk ↥(F ⊓ N) = rk ↥(N ⊓ F) := by rw [inf_comm]
  have h7 : rk ↥F ≤ rk Q := by
    have := rk_mono (le_top : F ≤ ⊤)
    rwa [rk_top] at this
  have h8 : rk ↥((⊤ : Subgroup (QuotMod N hN)) ⊓ F') = rk ↥F' := by rw [top_inf_eq]
  have h9 : rk ↥F' ≤ rk ↥(⊤ : Subgroup (QuotMod N hN)) := rk_mono le_top
  rw [h8]
  have h10 : rk ↥(⊤ : Subgroup Q) = rk Q := rk_top
  have h11 : rk ↥((⊤ : Subgroup Q) ⊓ F) = rk ↥F := by rw [top_inf_eq]
  rw [h11, h10]
  omega

@[expose, instance_reducible] def subAct (V : Subgroup Q) (hV : ∀ g : Γ, ∀ v ∈ V, g • v ∈ V) :
    MulDistribMulAction Γ ↥V where
  smul g v := ⟨g • (v : Q), hV g v v.2⟩
  one_smul _ := Subtype.ext (one_smul Γ _)
  mul_smul a b _ := Subtype.ext (mul_smul a b _)
  smul_mul a _ _ := Subtype.ext (smul_mul' a _ _)
  smul_one a := Subtype.ext (smul_one a)

end CFSG.Quasithin.Z391
