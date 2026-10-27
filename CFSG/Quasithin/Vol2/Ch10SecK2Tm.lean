module

public import CFSG.Quasithin.Background.C126NatDSimple
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin

section Levi

variable {A B : Type} [Group A] [Group B] {f : A →* B}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem comap_pCore_le_of_levi (hf : Function.Surjective f) (h4 : 4 ≤ Nat.card F)
    (e : A ⧸ CFSG.pCore 2 A ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hB : ¬ IsPGroup 2 B) :
    (CFSG.pCore 2 B).comap f ≤ CFSG.pCore 2 A := by
  have := C126.Nat.isSimpleGroup_sl2 h4
  set N := (CFSG.pCore 2 B).comap f with hN
  have hNn : N.Normal := (CFSG.pCore_normal (p := 2) (G := B)).comap f
  set N' := (N.map (QuotientGroup.mk' (CFSG.pCore 2 A))).map e.toMonoidHom with hN'
  have hN'n : N'.Normal :=
    (hNn.map _ (QuotientGroup.mk'_surjective _)).map _ e.surjective
  rcases hN'n.eq_bot_or_eq_top with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 A) x ∈ (⊥ : Subgroup (A ⧸ CFSG.pCore 2 A)) := by
      have : e (QuotientGroup.mk' (CFSG.pCore 2 A) x) ∈ N' := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [h, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at this
      exact this
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · exfalso
    apply hB
    have hsup : N ⊔ CFSG.pCore 2 A = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have ha : e (QuotientGroup.mk' (CFSG.pCore 2 A) a) ∈ N' := h ▸ Subgroup.mem_top _
      obtain ⟨_, ⟨n, hn, rfl⟩, hne⟩ := ha
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 A) n = QuotientGroup.mk' (CFSG.pCore 2 A) a :=
        e.injective hne
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have := Subgroup.mul_mem_sup hn h1
      rwa [mul_inv_cancel_left] at this
    have : ((CFSG.pCore 2 A).map f).Normal := (CFSG.pCore_normal (p := 2) (G := A)).map f hf
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 B) ⊔ (CFSG.pCore 2 A).map f) :=
      IsPGroup.to_sup_of_normal_right (CFSG.pCore_isPGroup (p := 2) (G := B))
        ((CFSG.pCore_isPGroup (p := 2) (G := A)).map f)
    have htop : (CFSG.pCore 2 B) ⊔ (CFSG.pCore 2 A).map f = ⊤ := by
      rw [eq_top_iff]
      intro b _
      obtain ⟨a, rfl⟩ := hf b
      have ha : f a ∈ (N ⊔ CFSG.pCore 2 A).map f :=
        Subgroup.mem_map_of_mem f (hsup ▸ Subgroup.mem_top a)
      rw [Subgroup.map_sup] at ha
      exact sup_le_sup_right (Subgroup.map_comap_le _ _) _ ha
    intro b
    obtain ⟨k, hk⟩ := hP ⟨b, htop ▸ Subgroup.mem_top b⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem pCore_eq_map_of_levi (hf : Function.Surjective f) (h4 : 4 ≤ Nat.card F)
    (e : A ⧸ CFSG.pCore 2 A ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hB : ¬ IsPGroup 2 B) :
    f.ker ≤ CFSG.pCore 2 A ∧ CFSG.pCore 2 B = (CFSG.pCore 2 A).map f := by
  have hle := comap_pCore_le_of_levi hf h4 e hB
  refine ⟨le_trans (fun x hx => ?_) hle, le_antisymm ?_ ?_⟩
  · show f x ∈ CFSG.pCore 2 B
    rw [MonoidHom.mem_ker.mp hx]
    exact Subgroup.one_mem _
  · rw [← Subgroup.map_comap_eq_self_of_surjective hf (CFSG.pCore 2 B)]
    exact Subgroup.map_mono hle
  · exact le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := A)).map f hf,
      (CFSG.pCore_isPGroup (p := 2) (G := A)).map f⟩

theorem nonempty_levi_of_map (hf : Function.Surjective f) (h4 : 4 ≤ Nat.card F)
    (e : A ⧸ CFSG.pCore 2 A ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hB : ¬ IsPGroup 2 B) :
    Nonempty (B ⧸ CFSG.pCore 2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨hker, hp⟩ := pCore_eq_map_of_levi hf h4 e hB
  let g : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgk : g.ker = CFSG.pCore 2 A := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hp]
    constructor
    · rintro ⟨a', ha', h⟩
      have hk : a'⁻¹ * a ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      have := (CFSG.pCore 2 A).mul_mem ha' (hker hk)
      rwa [mul_inv_cancel_left] at this
    · intro ha
      exact ⟨a, ha, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)).symm.trans e⟩

end Levi

theorem eq_of_card_sl2 {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (h : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1)) : q = q' := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ hq'
  zify [h1, h2] at h
  have ha : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hb : (1 : ℤ) ≤ q' := by exact_mod_cast hq'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlt' : (q : ℤ) < q' := by exact_mod_cast hlt
    have hp : (0 : ℤ) < (q' - q) * (q' ^ 2 + q * q' + q ^ 2 - 1) :=
      mul_pos (sub_pos.mpr hlt') (by nlinarith)
    nlinarith
  · have hgt' : (q' : ℤ) < q := by exact_mod_cast hgt
    have hp : (0 : ℤ) < (q - q') * (q ^ 2 + q * q' + q' ^ 2 - 1) :=
      mul_pos (sub_pos.mpr hgt') (by nlinarith)
    nlinarith

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
