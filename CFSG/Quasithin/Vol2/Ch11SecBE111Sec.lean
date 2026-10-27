module

public import CFSG.Quasithin.Vol2.Ch11SecBNPCase
public import CFSG.Quasithin.Background.E1ElevenIso

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def E111Prop (n : ℕ) : GrpPred := fun X _ =>
  Finite X → ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
    IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range) (MulAut.conj : X →* MulAut X).range →
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) ≤ (n : ℕ∞)

theorem map_range_conj_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (MulAut.conj : A →* MulAut A).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : B →* MulAut B).range := by
  ext φ
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨e a, ?_⟩
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro ⟨b, rfl⟩
    refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem isoInv_e111Prop (n : ℕ) : IsoInv (E111Prop n) := by
  intro A B _ _ e hB hA BA hBA hsyl
  have : Finite B := Finite.of_equiv A e.toEquiv
  have : Finite (MulAut A) := Finite.of_injective (fun φ : MulAut A => (φ : A → A))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite (MulAut B) := Finite.of_injective (fun φ : MulAut B => (φ : B → B))
    fun _ _ h => MulEquiv.ext (congrFun h)
  set c := MulAut.congr e with hc
  have hInn := map_range_conj_congr e
  have hsyl' : IsSylowIn 2 (BA.map c.toMonoidHom ⊓ (MulAut.conj : B →* MulAut B).range)
      (MulAut.conj : B →* MulAut B).range := by
    rw [← hInn, ← Subgroup.map_inf _ _ _ c.injective]
    exact (E1.isSylowIn_map_mulEquiv c).mpr hsyl
  have h1 := hB inferInstance (BA.map c.toMonoidHom) (hBA.map _) hsyl'
  rw [← hInn, ← Subgroup.map_sup, E1.Eleven.nParam_map_mulEquiv] at h1
  exact h1

theorem open_isSubnormal_top {Y : Type*} [Group Y] {M : Subgroup Y} (h : M.IsSubnormal) :
    CFSG.Open.IsSubnormal M ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

theorem nonabelian_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : B, a * b ≠ b * a) : ∃ a b : A, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
  have := congrArg e h'
  simpa using this

theorem e111Hyp_iff_secAll {G : Type} [Group G] [Finite G] (n : ℕ) :
    ASInputs.E111Hyp G n ↔ SecAll G (E111Prop n) := by
  constructor
  · intro h H₁ N _ hsn hs hnab
    set K := N.map H₁.subtype with hK
    have hKH : K ≤ H₁ := Subgroup.map_subtype_le N
    have hKN : K.subgroupOf H₁ = N := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [show x = y from Subtype.ext hyx.symm]
      · intro hx
        exact ⟨x, hx, rfl⟩
    have : (K.subgroupOf H₁).Normal := by rw [hKN]; infer_instance
    let e : (↥H₁ ⧸ N) ≃* (↥H₁ ⧸ K.subgroupOf H₁) := QuotientGroup.quotientMulEquivOfEq hKN.symm
    have hs' : IsSimpleGroup (↥H₁ ⧸ K.subgroupOf H₁) := (MulEquiv.isSimpleGroup_congr e).mp hs
    have hnab' := nonabelian_of_mulEquiv e.symm hnab
    have hP : E111Prop n (↥H₁ ⧸ K.subgroupOf H₁) := fun _ B hB hBI =>
      h H₁ K hKH (open_isSubnormal_top hsn) hs' hnab' B hB hBI
    exact isoInv_e111Prop n _ _ e hP
  · intro h H K hKH _ hsn hs hnab B hB hBI
    exact h H (K.subgroupOf H) (isSubnormal_of_open hsn Subgroup.IsSubnormal.top) hs hnab
      inferInstance B hB hBI

theorem secAll_quotient {Q : Type} [Group Q] {P : GrpPred} (hP : IsoInv P) (N : Subgroup Q)
    [N.Normal] (h : SecAll Q P) : SecAll (Q ⧸ N) P := by
  intro Hb Nb _ hsn hs hnab
  set π := QuotientGroup.mk' N with hπ
  set H := Hb.comap π with hH
  have hHsn : H.IsSubnormal := hsn.comap π
  let ρ : ↥H →* ↥Hb := (π.comp H.subtype).codRestrict Hb fun x => x.2
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  set ψ : ↥H →* ↥Hb ⧸ Nb := (QuotientGroup.mk' Nb).comp ρ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective Nb).comp hρs
  let e : ↥H ⧸ ψ.ker ≃* ↥Hb ⧸ Nb := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  have hs' : IsSimpleGroup (↥H ⧸ ψ.ker) := (MulEquiv.isSimpleGroup_congr e).mpr hs
  exact hP _ _ e.symm (h H ψ.ker hHsn hs' (nonabelian_of_mulEquiv e hnab))

theorem secAll_subgroup_of_isSubnormal {Q : Type} [Group Q] {P : GrpPred} (hP : IsoInv P)
    {S : Subgroup Q} (hS : S.IsSubnormal) (h : SecAll Q P) : SecAll ↥S P := by
  intro H₁ N₁ _ hsn hs hnab
  set H₂ := H₁.map S.subtype with hH₂
  have hH₂sn : H₂.IsSubnormal := hsn.trans' hS
  let ι : ↥H₁ ≃* ↥H₂ := Subgroup.equivMapOfInjective H₁ S.subtype S.subtype_injective
  set N₂ : Subgroup ↥H₂ := N₁.map ι.toMonoidHom with hN₂
  have : N₂.Normal := Subgroup.Normal.map inferInstance _ ι.surjective
  let e : ↥H₁ ⧸ N₁ ≃* ↥H₂ ⧸ N₂ := QuotientGroup.congr N₁ N₂ ι rfl
  have hs' : IsSimpleGroup (↥H₂ ⧸ N₂) := (MulEquiv.isSimpleGroup_congr e).mp hs
  exact hP _ _ e (h H₂ N₂ hH₂sn hs' (nonabelian_of_mulEquiv e.symm hnab))

@[expose] def interEquiv {Y : Type} [Group Y] (H₁ N : Subgroup Y) :
    ↥(N.subgroupOf H₁) ≃* ↥(H₁.subgroupOf N) where
  toFun d := ⟨⟨((d : ↥H₁) : Y), d.2⟩, (d : ↥H₁).2⟩
  invFun d := ⟨⟨((d : ↥N) : Y), d.2⟩, (d : ↥N).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem secAll_of_normal_of_two_pow {Y : Type} [Group Y] [Finite Y] {P : GrpPred}
    (hP : IsoInv P) {N : Subgroup Y} [N.Normal] (h2 : ∀ y : Y, ∃ e : ℕ, y ^ 2 ^ e ∈ N)
    (h : SecAll ↥N P) : SecAll Y P := by
  intro H₁ N₁ _ hsn hs hnab
  set π := QuotientGroup.mk' N₁ with hπ
  set D : Subgroup ↥H₁ := N.subgroupOf H₁ with hD
  have hDn : D.Normal := inferInstance
  have hDm : (D.map π).Normal := hDn.map π (QuotientGroup.mk'_surjective N₁)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map π) with hbot | htop
  ·
    exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2q : IsPGroup 2 (↥H₁ ⧸ N₁) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₁ q
      obtain ⟨e, he⟩ := h2 (x : Y)
      refine ⟨e, ?_⟩
      have hxD : x ^ 2 ^ e ∈ D := by
        rw [hD, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact he
      have : π (x ^ 2 ^ e) ∈ D.map π := ⟨_, hxD, rfl⟩
      rw [hbot, Subgroup.mem_bot, map_pow] at this
      exact this
    have := h2q.isNilpotent
    exact not_nonabelian_of_isSolvable inferInstance hnab
  ·
    set ψ : ↥D →* ↥H₁ ⧸ N₁ := π.comp D.subtype with hψ
    have hψs : Function.Surjective ψ := by
      intro q
      have hq : q ∈ D.map π := by rw [htop]; trivial
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    let ε := interEquiv H₁ N
    set H₃ : Subgroup ↥N := H₁.subgroupOf N with hH₃
    have hH₃sn : H₃.IsSubnormal := hsn.subgroupOf
    set N₃ : Subgroup ↥H₃ := ψ.ker.map ε.toMonoidHom with hN₃
    have : N₃.Normal := Subgroup.Normal.map inferInstance _ ε.surjective
    let e₁ : ↥D ⧸ ψ.ker ≃* ↥H₃ ⧸ N₃ := QuotientGroup.congr ψ.ker N₃ ε rfl
    let e₂ : ↥D ⧸ ψ.ker ≃* ↥H₁ ⧸ N₁ := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
    let e : ↥H₁ ⧸ N₁ ≃* ↥H₃ ⧸ N₃ := e₂.symm.trans e₁
    have hs' : IsSimpleGroup (↥H₃ ⧸ N₃) := (MulEquiv.isSimpleGroup_congr e).mp hs
    exact hP _ _ e (h H₃ N₃ hH₃sn hs' (nonabelian_of_mulEquiv e.symm hnab))

theorem secAll_sup_of_normal {Q : Type} [Group Q] [Finite Q] {P : GrpPred} (hP : IsoInv P)
    {N T : Subgroup Q} [N.Normal] (hT : IsPGroup 2 T) (h : SecAll Q P) : SecAll ↥(N ⊔ T) P := by
  set Y := N ⊔ T with hY
  have hNY : N ≤ Y := le_sup_left
  have hsN : SecAll ↥N P :=
    secAll_subgroup_of_isSubnormal hP (Subgroup.Normal.isSubnormal inferInstance) h
  have hsN' : SecAll ↥(N.subgroupOf Y) P :=
    secAll_of_mulEquiv hP (Subgroup.subgroupOfEquivOfLe hNY) hsN
  refine secAll_of_normal_of_two_pow hP (N := N.subgroupOf Y) (fun y => ?_) hsN'
  obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hT (y : Q) y.2
  exact ⟨e, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact he⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
