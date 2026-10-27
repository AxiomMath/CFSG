module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGLift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent

public section

namespace CFSG.StandardType.UnitSixThreeKG

open CFSG CFSG.Assembly

private def twoPart {L' : Type} [Group L'] [Finite L'] (N : Subgroup L')
    (hN : N ≤ Subgroup.center L') : Subgroup L' where
  carrier := {z | z ∈ N ∧ z ^ (2 ^ Nat.card L') = 1}
  one_mem' := ⟨N.one_mem, one_pow _⟩
  mul_mem' := fun {x y} hx hy => ⟨N.mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (Subgroup.mem_center_iff.mp (hN hy.1) x), hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {x} hx => ⟨N.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem perLineOn_descent {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {I : Set (MulAut R)}
    (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l))
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        PerLineOn A₁) :
    PerLineOn A := by
  classical
  set Z := twoPart ψ.ker hker with hZdef
  have hZc : Z ≤ Subgroup.center L' := fun z hz => hker hz.1
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZc hy) g
  haveI hZn : Z.Normal := ⟨fun y hy g => by rw [hcen y hy g, mul_inv_cancel_right]; exact hy⟩
  have hZ2 : IsPGroup 2 Z := fun g => ⟨Nat.card L', Subtype.ext (by simpa using g.2.2)⟩
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  have hkerA : ∀ a ∈ A, ∀ z ∈ ψ.ker, a z ∈ ψ.ker := by
    intro a ha z hz
    obtain ⟨x, -, hx⟩ := hAI a ha
    rw [MonoidHom.mem_ker, ← hx, (MonoidHom.mem_ker).mp hz, map_one]
  have hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z := fun a ha z hz =>
    ⟨hkerA a ha z hz.1, by rw [← map_pow, hz.2, map_one]⟩
  have hmap : ∀ a ∈ A, Z.map a.toMonoidHom = Z := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact hZA a ha z hz
    · intro z hz
      refine ⟨a⁻¹ z, hZA _ (A.inv_mem ha) z hz, ?_⟩
      simp
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  let ρf : A → MulAut (L' ⧸ Z) := fun a => QuotientGroup.congr Z Z a.1 (hmap a.1 a.2)
  have hρf : ∀ (a : A) (l : L'), ρf a (l : L' ⧸ Z) = ((a.1 l : L') : L' ⧸ Z) := fun a l =>
    QuotientGroup.congr_mk _ _ _ _ l
  let ρ : A →* MulAut (L' ⧸ Z) :=
    { toFun := ρf
      map_one' := by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        rw [hρf]; rfl
      map_mul' := fun a b => by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        simp only [MulAut.mul_apply, hρf]
        rfl }
  have hρ : ∀ (a : A) (l : L'), ρ a (l : L' ⧸ Z) = ((a.1 l : L') : L' ⧸ Z) := hρf
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfixl : ∀ l : L', l⁻¹ * a.1 l ∈ Z := by
      intro l
      have := hρ a l
      rw [ha, MulAut.one_apply] at this
      exact QuotientGroup.eq.mp this
    letI : CommGroup Z :=
      { (inferInstance : Group Z) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
    let f : L' →* Z :=
      { toFun := fun l => ⟨l⁻¹ * a.1 l, hfixl l⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun l m => Subtype.ext (by
          show (l * m)⁻¹ * a.1 (l * m) = l⁻¹ * a.1 l * (m⁻¹ * a.1 m)
          have hc := hcen _ (hfixl l) m⁻¹
          calc (l * m)⁻¹ * a.1 (l * m) = m⁻¹ * (l⁻¹ * a.1 l) * a.1 m := by rw [map_mul]; group
            _ = (l⁻¹ * a.1 l) * m⁻¹ * a.1 m := by rw [hc]
            _ = l⁻¹ * a.1 l * (m⁻¹ * a.1 m) := by group) }
    have hf : ∀ l, f l = 1 := fun l =>
      Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
    apply Subtype.ext
    ext l
    have h1 : l⁻¹ * a.1 l = 1 := congrArg Subtype.val (hf l)
    exact (inv_mul_eq_one.mp h1).symm
  set A₁ := ρ.range with hA₁def
  have hA₁ : CFSG.Open.IsElemAbelian 3 A₁ := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      have : a * b = b * a := Subtype.ext (hAc a.1 a.2 b.1 b.2)
      rw [← map_mul, this, map_mul]
    · rintro _ ⟨a, rfl⟩
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hAp a.1 a.2)
      rw [← map_pow, this, map_one]
  have hcardA : Nat.card A₁ = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hZψ : Z ≤ ψ.ker := fun z hz => hz.1
  let ψ₁ : L' ⧸ Z →* R := QuotientGroup.lift Z ψ hZψ
  have hψ₁ : ∀ l : L', ψ₁ (l : L' ⧸ Z) = ψ l := fun l => QuotientGroup.lift_mk _ _ _
  have hψ₁s : Function.Surjective ψ₁ := fun r => by
    obtain ⟨l, rfl⟩ := hψ r; exact ⟨l, hψ₁ l⟩
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (L' ⧸ Z) := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hl : l ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hψ₁]; exact hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hl) g]
  have hperf₁ : commutator (L' ⧸ Z) = ⊤ := by
    have : (commutator L').map (QuotientGroup.mk' Z) = commutator (L' ⧸ Z) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hπs]
    rw [← this, hperf, Subgroup.map_top_of_surjective _ hπs]
  have hodd : Odd (Nat.card ψ₁.ker) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective x.1
    have hx2 : x.1 ^ 2 = 1 := by
      have := congrArg Subtype.val (pow_orderOf_eq_one x)
      rw [hx] at this; simpa using this
    have hl2 : l ^ 2 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hl, hx2]
    have hlker : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₁, hl]; exact x.2
    have hlZ : l ∈ Z := ⟨hlker, Line63.pow_two_pow_card l (j := Nat.card L' + 1)
      (by rw [pow_succ, pow_mul', hl2.2])⟩
    have : x = 1 := Subtype.ext (by rw [← hl]; exact (QuotientGroup.eq_one_iff l).mpr hlZ)
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hAI₁ : ∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L' ⧸ Z, x (ψ₁ l) = ψ₁ (a l) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hAI a.1 a.2
    refine ⟨x, hx, fun l => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    rw [hψ₁, hρ, hψ₁]; exact hxa l
  have hPerLine₁ : PerLineOn A₁ :=
    H (L' ⧸ Z) ψ₁ hψ₁s hψ₁ker hperf₁ hodd A₁ hA₁ hAI₁ hcardA
  intro a₀ ha₀ ha₀ne hcyc
  let a₀' : A := ⟨a₀, ha₀⟩
  set a₁ : MulAut (L' ⧸ Z) := ρ a₀' with ha₁def
  have ha₁ : a₁ ∈ A₁ := ⟨a₀', ha₁def.symm⟩
  have ha₁ne : a₁ ≠ 1 := by
    intro h1
    have h2 : a₀' = 1 := hρinj (by rw [← ha₁def, h1, map_one])
    exact ha₀ne (Subtype.ext_iff.mp h2)
  have hc₁ : ∀ l : L', a₁ ((QuotientGroup.mk' Z) l) = (QuotientGroup.mk' Z) (a₀ l) := by
    intro l
    rw [ha₁def, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact hρ a₀' l
  have hcyc₁ : GGFixCompCyclic 3 a₁ :=
    ggFixCompCyclic_map (QuotientGroup.mk'_surjective Z)
      (by rw [QuotientGroup.ker_mk']; exact hZc) hc₁ hcyc
  obtain ⟨n₁, hn₁, hmv₁⟩ := hPerLine₁ a₁ ha₁ ha₁ne hcyc₁
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective n₁
  have hu : ∀ a : A, ((n₀ * (a.1 n₀)⁻¹ : L') : L' ⧸ Z) =
      (n₀ : L' ⧸ Z) * (ρ a (n₀ : L' ⧸ Z))⁻¹ :=
    fun a => by rw [hρ, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h3 : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ Z := by
    intro a ha
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu ⟨a, ha⟩]
    exact (hn₁ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
  have hfix : ∀ a ∈ A, ∀ a' ∈ A, (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ Z := by
    intro a ha a' ha'
    apply QuotientGroup.eq.mp
    rw [show ((a' (n₀ * (a n₀)⁻¹) : L') : L' ⧸ Z) =
        ρ ⟨a', ha'⟩ ((n₀ * (a n₀)⁻¹ : L') : L' ⧸ Z) from (hρ ⟨a', ha'⟩ _).symm, hu ⟨a, ha⟩]
    exact ((hn₁ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).2 _ ⟨⟨a', ha'⟩, rfl⟩).symm
  obtain ⟨z, hz, hzW⟩ := Line63.exists_lift_fixed hZc hZ2 hA3 hAc hZA n₀ h3 hfix
  refine ⟨n₀ * z, hzW, ?_⟩
  intro hmem
  have hz1 : ((z : L') : L' ⧸ Z) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  have hmk : (((n₀ * z : L') : L' ⧸ Z)) = (n₀ : L' ⧸ Z) := by
    rw [QuotientGroup.mk_mul, hz1, mul_one]
  set g := MulAut.conj (n₀ * z) * a₀ * (MulAut.conj (n₀ * z))⁻¹ with hgdef
  have hgA : g ∈ A := (Subgroup.zpowers_le.mpr ha₀) hmem
  have hkey : ρ ⟨g, hgA⟩ =
      MulAut.conj (n₀ : L' ⧸ Z) * a₁ * (MulAut.conj (n₀ : L' ⧸ Z))⁻¹ := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hρ]
    change ((g l : L') : L' ⧸ Z) =
      (MulAut.conj (n₀ : L' ⧸ Z) * a₁ * (MulAut.conj (n₀ : L' ⧸ Z))⁻¹) (l : L' ⧸ Z)
    rw [hgdef]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk]
    rw [← hρ a₀' ((n₀ * z)⁻¹ * l * (n₀ * z)), ← ha₁def]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk]
  have hmem₁ : MulAut.conj (n₀ : L' ⧸ Z) * a₁ * (MulAut.conj (n₀ : L' ⧸ Z))⁻¹ ∈
      Subgroup.zpowers a₁ := by
    rw [← hkey]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hgzp : (⟨g, hgA⟩ : A) ∈ Subgroup.zpowers a₀' := by
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa using hk
    have := Subgroup.mem_map_of_mem ρ hgzp
    rwa [MonoidHom.map_zpowers, ← ha₁def] at this
  exact hmv₁ hmem₁

end CFSG.StandardType.UnitSixThreeKG

end
