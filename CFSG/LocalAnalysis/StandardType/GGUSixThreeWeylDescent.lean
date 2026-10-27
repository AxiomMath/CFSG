module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord

public section

namespace CFSG.StandardType

open Line63 (exists_lift_fixed pow_two_pow_card)

private theorem eq_of_forall_inv_mul_mem_of_perfect {L' : Type} [Group L'] {Z : Subgroup L'}
    (hZ : Z ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {φ₁ φ₂ : MulAut L'}
    (h : ∀ l, (φ₁ l)⁻¹ * φ₂ l ∈ Z) : φ₁ = φ₂ := by
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
  let f : L' →* Z :=
    { toFun := fun l => ⟨(φ₁ l)⁻¹ * φ₂ l, h l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show (φ₁ (l * m))⁻¹ * φ₂ (l * m) = (φ₁ l)⁻¹ * φ₂ l * ((φ₁ m)⁻¹ * φ₂ m)
        have hc := hcen _ (h l) (φ₁ m)⁻¹
        calc (φ₁ (l * m))⁻¹ * φ₂ (l * m) = (φ₁ m)⁻¹ * ((φ₁ l)⁻¹ * φ₂ l) * φ₂ m := by
              rw [map_mul, map_mul]; group
          _ = (φ₁ l)⁻¹ * φ₂ l * (φ₁ m)⁻¹ * φ₂ m := by rw [hc]
          _ = (φ₁ l)⁻¹ * φ₂ l * ((φ₁ m)⁻¹ * φ₂ m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
  ext l
  exact inv_mul_eq_one.mp (congrArg Subtype.val (hf l))

theorem ggTorusReflGenW_three_of_oddKernel {r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R) (A₁ : Subgroup (MulAut L₁)),
      GGTorusTBGroup 3 r R I L₁ ψ₁ A₁ → Odd (Nat.card ψ₁.ker) →
        ggAutomizer (MulAut.conj : L₁ →* MulAut L₁).range A₁ ≤
          Subgroup.closure (ggTorusReflSet 3 A₁)) :
    GGTorusReflGenW 3 r R I := by
  classical
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  let Z : Subgroup L' :=
    { carrier := {z | z ∈ ψ.ker ∧ z ^ (2 ^ Nat.card L') = 1}
      one_mem' := ⟨ψ.ker.one_mem, one_pow _⟩
      mul_mem' := fun {x y} hx hy => ⟨ψ.ker.mul_mem hx.1 hy.1, by
        rw [Commute.mul_pow (Subgroup.mem_center_iff.mp (hker hy.1) x), hx.2, hy.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨ψ.ker.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hmemZ : ∀ z, z ∈ Z ↔ z ∈ ψ.ker ∧ z ^ (2 ^ Nat.card L') = 1 := fun z => Iff.rfl
  have hZc : Z ≤ Subgroup.center L' := fun z hz => hker ((hmemZ z).1 hz).1
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZc hy) g
  haveI hZn : Z.Normal := ⟨fun y hy g => by rw [hcen y hy g, mul_inv_cancel_right]; exact hy⟩
  have hZ2 : IsPGroup 2 Z := fun g =>
    ⟨Nat.card L', Subtype.ext (by simpa using ((hmemZ g.1).1 g.2).2)⟩
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  have hkerA : ∀ a ∈ A, ∀ z ∈ ψ.ker, a z ∈ ψ.ker := by
    intro a ha z hz
    obtain ⟨x, -, hx⟩ := hAI a ha
    rw [MonoidHom.mem_ker, ← hx, (MonoidHom.mem_ker).mp hz, map_one]
  have hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z := fun a ha z hz => (hmemZ _).2
    ⟨hkerA a ha z ((hmemZ z).1 hz).1, by rw [← map_pow, ((hmemZ z).1 hz).2, map_one]⟩
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
    have h1 : (1 : MulAut L') = a.1 := eq_of_forall_inv_mul_mem_of_perfect hZc hperf fun l => by
      have := hρ a l
      rw [ha, MulAut.one_apply] at this
      exact QuotientGroup.eq.mp this
    exact Subtype.ext h1.symm
  have hconj : ∀ (m : L') (a : A) (hma : MulAut.conj m * a.1 * (MulAut.conj m)⁻¹ ∈ A),
      MulAut.conj (m : L' ⧸ Z) * ρ a * (MulAut.conj (m : L' ⧸ Z))⁻¹ = ρ ⟨_, hma⟩ := by
    intro m a hma
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    rw [hρ ⟨_, hma⟩]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hρ,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
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
  have hZψ : Z ≤ ψ.ker := fun z hz => ((hmemZ z).1 hz).1
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
    have hlZ : l ∈ Z := (hmemZ l).2 ⟨hlker, pow_two_pow_card l (j := Nat.card L' + 1)
      (by rw [pow_succ, pow_mul', ((hmemZ _).1 hl2).2])⟩
    have : x = 1 := Subtype.ext (by rw [← hl]; exact (QuotientGroup.eq_one_iff l).mpr hlZ)
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hAI₁ : ∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L' ⧸ Z, x (ψ₁ l) = ψ₁ (a l) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hAI a.1 a.2
    refine ⟨x, hx, fun l => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    rw [hψ₁, hρ, hψ₁]; exact hxa l
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
  have hmZ : ∀ z ∈ Z, z ^ ((2 ^ k) ^ 2) = 1 := by
    intro z hz
    have : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hk] at this
    have h' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val this
    rw [sq, pow_mul, h', one_pow]
  obtain ⟨j, hj⟩ : ∃ j, (2 ^ k) ^ 2 = 3 * j + 1 := ⟨((2 ^ k) ^ 2 - 1) / 3, by
    have : (2 ^ k) ^ 2 % 3 = 1 := by rw [← pow_mul, pow_mul', Nat.pow_mod]; norm_num
    omega⟩
  have hsc₁ : GGTorusSelfCent 3 A₁ := by
    intro x hxfix hx3
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hl3 : l ^ 3 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx3]
    have hlfix : ∀ a ∈ A, l⁻¹ * a l ∈ Z := fun a ha => by
      apply QuotientGroup.eq.mp
      rw [← hρ ⟨a, ha⟩]
      exact (hxfix _ ⟨⟨a, ha⟩, rfl⟩).symm
    set t := l ^ ((2 ^ k) ^ 2) with htdef
    have ht3 : t ^ 3 = 1 := by
      rw [htdef, ← pow_mul, mul_comm, pow_mul]; exact hmZ _ hl3
    have htfix : ∀ a ∈ A, a t = t := by
      intro a ha
      have : a l = l * (l⁻¹ * a l) := by group
      rw [htdef, map_pow, this, Commute.mul_pow (hcen _ (hlfix a ha) l), hmZ _ (hlfix a ha),
        mul_one]
    have htA := hsc t htfix ht3
    have htmk : ((t : L') : L' ⧸ Z) = (l : L' ⧸ Z) := by
      rw [htdef, QuotientGroup.mk_pow, hj, pow_succ, pow_mul, hx3, one_pow, one_mul]
    refine ⟨⟨_, htA⟩, ?_⟩
    ext y
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hρ ⟨_, htA⟩, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, htmk]
  have hTB₁ : GGTorusTBGroup 3 r R I (L' ⧸ Z) ψ₁ A₁ :=
    ⟨hψ₁s, hψ₁ker, hperf₁, hA₁, hAI₁, hcardA ▸ hr, hcardA ▸ h3, hsc₁⟩
  have H₁ := H (L' ⧸ Z) ψ₁ A₁ hTB₁ hodd
  let e : A ≃* A₁ := MonoidHom.ofInjective hρinj
  have he : ∀ a : A, ((e a : A₁) : MulAut (L' ⧸ Z)) = ρ a := fun a => rfl
  have hcongr : ∀ (φ₁ : MulAut A₁) (φ : MulAut A),
      (∀ a : A, ((φ₁ (e a) : A₁) : MulAut (L' ⧸ Z)) = ρ (φ a)) → MulAut.congr e.symm φ₁ = φ := by
    intro φ₁ φ hφ
    refine MulEquiv.ext fun a => ?_
    show e.symm (φ₁ (e.symm.symm a)) = φ a
    rw [MulEquiv.symm_symm, MulEquiv.symm_apply_eq]
    exact Subtype.ext ((hφ a).trans (he (φ a)).symm)
  have hrefl : ∀ φ₁ ∈ ggTorusReflSet 3 A₁, MulAut.congr e.symm φ₁ ∈ ggTorusReflSet 3 A := by
    rintro _ ⟨n₁, hn₁, hW₁, rfl, hR₁⟩
    obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective n₁
    have hu : ∀ a : A,
        ((n₀ * (a.1 n₀)⁻¹ : L') : L' ⧸ Z) = (n₀ : L' ⧸ Z) * (ρ a (n₀ : L' ⧸ Z))⁻¹ :=
      fun a => by rw [hρ, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h3' : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ Z := by
      intro a ha
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu ⟨a, ha⟩]
      exact (hW₁ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
    have hfix : ∀ a ∈ A, ∀ a' ∈ A, (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ Z := by
      intro a ha a' ha'
      apply QuotientGroup.eq.mp
      rw [show ((a' (n₀ * (a n₀)⁻¹) : L') : L' ⧸ Z) =
          ρ ⟨a', ha'⟩ ((n₀ * (a n₀)⁻¹ : L') : L' ⧸ Z) from (hρ ⟨a', ha'⟩ _).symm, hu ⟨a, ha⟩]
      exact ((hW₁ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).2 _ ⟨⟨a', ha'⟩, rfl⟩).symm
    obtain ⟨z, hz, hzW⟩ := exists_lift_fixed hZc hZ2 hA3 hAc hZA n₀ h3' hfix
    have hW : GGTorusWeylElt 3 A (n₀ * z) := hzW
    have hnN := conj_mem_normalizer_of_torusWeylElt hsc hW
    have hz1 : ((z : L') : L' ⧸ Z) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    have hmk : ((n₀ * z : L') : L' ⧸ Z) = (n₀ : L' ⧸ Z) := by
      rw [QuotientGroup.mk_mul, hz1, mul_one]
    refine ⟨n₀ * z, hnN, hW, hcongr _ _ fun a => ?_, ggIsReflection_congr e.symm hR₁.1 hR₁.2⟩
    have key := hconj (n₀ * z) a ((Subgroup.mem_normalizer_iff.mp hnN a).mp a.2)
    rw [hmk] at key
    rw [ggConjAut_apply, he]
    exact key
  intro v hv
  obtain ⟨g, ⟨m, rfl⟩, hgN, hvg⟩ := mem_ggAutomizer_iff.mp hv
  have hg₁N : MulAut.conj (m : L' ⧸ Z) ∈ Subgroup.normalizer (A₁ : Set (MulAut (L' ⧸ Z))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (hconj m a ((Subgroup.mem_normalizer_iff.mp hgN a).mp a.2)).symm⟩
    · rintro ⟨b, hb⟩
      have hm' : MulAut.conj m⁻¹ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
        rw [map_inv]; exact Subgroup.inv_mem _ hgN
      have hb' := (Subgroup.mem_normalizer_iff.mp hm' b).mp b.2
      refine ⟨_, (hconj m⁻¹ b hb').symm.trans ?_⟩
      rw [hb, QuotientGroup.mk_inv, map_inv]
      group
  have hv₁ := H₁ (ggConjAut_mem_ggAutomizer (H := (MulAut.conj : (L' ⧸ Z) →* _).range)
    ⟨(m : L' ⧸ Z), rfl⟩ hg₁N)
  have hvv : MulAut.congr e.symm (ggConjAut A₁ hg₁N) = v := by
    refine hcongr _ _ fun a => ?_
    rw [ggConjAut_apply, he, hconj m a ((Subgroup.mem_normalizer_iff.mp hgN a).mp a.2)]
    congr 1
    exact Subtype.ext (hvg a).symm
  let F : MulAut A₁ →* MulAut A := (MulAut.congr e.symm).toMonoidHom
  have hmem : F (ggConjAut A₁ hg₁N) ∈ (Subgroup.closure (ggTorusReflSet 3 A₁)).map F :=
    Subgroup.mem_map_of_mem F hv₁
  rw [MonoidHom.map_closure] at hmem
  rw [← hvv]
  exact Subgroup.closure_mono (by rintro _ ⟨φ₁, hφ₁, rfl⟩; exact hrefl φ₁ hφ₁) hmem

end CFSG.StandardType

end
