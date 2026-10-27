module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6TwoLang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Upper
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit)

section Frame

variable {τ : Tag} {Lf : Type} [Field Lf] {X : Type} [Group X]
  {Γ : Subgroup (ModGL τ Lf)} {G₀ B : Subgroup X}

theorem GGTCUFrame.JLang_mono (fr : GGTCUFrame Γ G₀ B) {J L : Subgroup X} (hJL : J ≤ L) :
    fr.JLang J ≤ fr.JLang L := by
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  exact ⟨_, ⟨j, hJL hj, rfl⟩, rfl⟩

theorem GGTCUFrame.toLang_mem_DLang (fr : GGTCUFrame Γ G₀ B) {D : Subgroup X} (hDB : D ≤ B)
    {x : X} (hx : x ∈ D) :
    fr.toLang ⟨x, hDB hx⟩ ∈ fr.DLang D :=
  ⟨_, ⟨⟨x, hDB hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩, rfl⟩

theorem GGTCUFrame.DLang_zpowers_le (fr : GGTCUFrame Γ G₀ B) {x : X} (hx : x ∈ B) :
    fr.DLang (Subgroup.zpowers x) ≤ Subgroup.zpowers (fr.toLang ⟨x, hx⟩) := by
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hb)
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  have hb' : b = ⟨x, hx⟩ ^ n := Subtype.ext (by simpa using hn.symm)
  rw [hb', map_zpow, map_zpow]
  rfl

theorem centralizer_zpowers_eq_single {G : Type*} [Group G] (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem GGTCUFrame.centralizer_DLang_zpowers (fr : GGTCUFrame Γ G₀ B) {x : X} (hx : x ∈ B) :
    Subgroup.centralizer ((fr.DLang (Subgroup.zpowers x) : Subgroup (ModGL τ Lf)) :
      Set (ModGL τ Lf)) = Subgroup.centralizer {fr.toLang ⟨x, hx⟩} := by
  have hDB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hx
  have h1 : fr.toLang ⟨x, hx⟩ ∈ fr.DLang (Subgroup.zpowers x) :=
    fr.toLang_mem_DLang hDB (Subgroup.mem_zpowers x)
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 h1)
  · calc Subgroup.centralizer {fr.toLang ⟨x, hx⟩}
        = Subgroup.centralizer ((Subgroup.zpowers (fr.toLang ⟨x, hx⟩) :
            Subgroup (ModGL τ Lf)) : Set (ModGL τ Lf)) :=
          (centralizer_zpowers_eq_single _).symm
      _ ≤ _ := Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (fr.DLang_zpowers_le hx))

theorem GGTCUFrame.le_centralizer_of_lang_commute (fr : GGTCUFrame Γ G₀ B) {D L : Subgroup X}
    (hDB : D ≤ B) (hLG : L ≤ G₀) (hL : commutator ↥L = ⊤)
    (hcomm : fr.JLang L ≤
      Subgroup.centralizer ((fr.DLang D : Subgroup (ModGL τ Lf)) : Set (ModGL τ Lf))) :
    D ≤ Subgroup.centralizer (L : Set X) := by
  intro d hd
  obtain ⟨n, hn1, hn2⟩ := fr.act ⟨d, hDB hd⟩
  have hcomm' : ∀ j : ↥G₀, (j : X) ∈ L →
      fr.ν ⟨d, hDB hd⟩ * QuotientGroup.mk j = QuotientGroup.mk j * fr.ν ⟨d, hDB hd⟩ := by
    intro j hj
    have hjm : fr.embLang (QuotientGroup.mk j) ∈ fr.JLang L :=
      ⟨_, ⟨j, (Subgroup.mem_subgroupOf.2 hj), rfl⟩, rfl⟩
    have hdm : fr.embLang (fr.ν ⟨d, hDB hd⟩) ∈ fr.DLang D :=
      ⟨_, ⟨⟨d, hDB hd⟩, Subgroup.mem_subgroupOf.2 hd, rfl⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hcomm hjm) _ hdm
    apply fr.embLang_injective
    simpa [map_mul] using this
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := commute_of_inner_action_on_perfect hLG hL hn2
    (fun j hj => by rw [hn1]; exact hcomm' j hj) l hl
  exact this.symm

end Frame

theorem false_of_labelA5 (hRig : GGLabelRigidInput) {Y : Type} [Group Y] {L : Subgroup Y}
    {p f : ℕ} (hp3 : p ≠ 3) (hc : orderOf ((2 : ZMod p) ^ f) = 2)
    (hsplit : LargeEvenMarking ↥L fun lab _ _ _ _ _ => LargeEvenSplit p lab)
    (hlab : GGHasLabel ⟨LargeEvenLieTag.A, 5, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (hΛ : LargeEvenInLambda2 ⟨LargeEvenLieTag.A, 5, f⟩) : False := by
  obtain ⟨lab', hΛ', hlab', R, _, I, F, θ, hsp⟩ := largeEvenMarking_exists_hasLabel hsplit
  have hiso := hRig _ _ _ hΛ hΛ' hlab hlab'
  have heq : lab' = ⟨LargeEvenLieTag.A, 5, f⟩ := by
    rcases hiso with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact h.symm
    all_goals simp at h
  rw [heq] at hsp
  rcases hsp with ⟨-, hd⟩ | ⟨hnu, -⟩ | ⟨h3, -⟩ | ⟨-, hp3'⟩
  · have h1 : ((2 ^ f - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (2 ^ f - 1) p).2 hd
    rw [Nat.cast_sub Nat.one_le_two_pow] at h1
    push_cast at h1
    have h2 : (2 : ZMod p) ^ f = 1 := sub_eq_zero.1 h1
    rw [h2, orderOf_one] at hc
    omega
  · exact hnu trivial
  · rcases h3 with h3 | h3 <;> simp at h3
  · exact hp3 hp3'

theorem false_E6_two_of_inputs
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E6 f) (hc : orderOf ((2 : ZMod p) ^ f) = 2) (hp : p ≠ 3) :
    False := by
  have hp2 := h.ne_two
  have hp5 : 5 ≤ p := by
    have h2 := h.prime.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd h.prime (by decide)
    omega
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .E6 p (Nat.card B) :=
    utoralAt_of_nonTorsion h.prime hp2 (fun _ => hp) (fun h => by cases h) hBpos
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨K, _, _, _, S₁, fr₁, hq, hBT, ⟨w, hρ⟩, a, i, ha, hap, hspan, h2, hΨ, horth, hcard,
      hrk⟩ :=
    uframe_data (uFieldInput_of_SL hR (Or.inl rfl)) (Or.inr (Or.inl rfl)) h.prime hp2 hmod
      h.b_norm (h.inner_E6 (Or.inl hp)) h.b_faithful h.b_elem h.d_le h.d_card
      (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
      ⟨t', m, f', hlt, hm⟩ hTor
  have hr2 : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) = 2 := by
    have hle := e6_finrank_le_two hΨ S₁.frob.iform_eq horth
    by_contra hne
    have hlt2 : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) < 2 := by
      omega
    have hpow : p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) <
        p ^ 4 :=
      Nat.pow_lt_pow_right (by have := h.prime.two_le; omega) (by omega)
    have h4 := h.b_card
    omega
  have hDcard : Nat.card ↥(fr₁.DLang D) = p ^ 2 := by
    rw [fr₁.card_DLang h.d_le, h.d_card]
  have hT : ∀ u : ↥(fr₁.DLang D), rootDiagUnit .E6 (a u) ∈ S₁.D.torus := fun u =>
    (ha u) ▸ hBT (fr₁.DLang_le_BLang u.2)
  have hxB : x ∈ B := h.d_le h.x_mem
  have hxD : fr₁.toLang ⟨x, hxB⟩ ∈ fr₁.DLang D := fr₁.toLang_mem_DLang h.d_le h.x_mem
  have hx1 : (⟨fr₁.toLang ⟨x, hxB⟩, hxD⟩ : ↥(fr₁.DLang D)) ≠ 1 := by
    intro h1
    have h2 : fr₁.toLang ⟨x, hxB⟩ = 1 := congrArg Subtype.val h1
    have h3 : (⟨x, hxB⟩ : ↥B) = 1 := fr₁.toLang_injective (h2.trans (map_one fr₁.toLang).symm)
    exact h.x_ne (congrArg Subtype.val h3)
  have hJc := fr₁.isComponentOf_JLang h.d_le (h.j_comp.1.trans inf_le_left)
    (Assembly.isComponentOf_iff_open.1 h.j_comp)
  have hLG : L ≤ G₀ := h.l_le
  have hLq : CFSG.Open.IsQuasisimple ↥L := (Assembly.isComponentOf_iff_open.1 h.l_comp).2.2
  have hLc0 := fr₁.isComponentOf_JLang (D := Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxB)
    hLG (by
      rw [centralizer_zpowers_eq_single]
      exact Assembly.isComponentOf_iff_open.1 h.l_comp)
  rw [fr₁.centralizer_DLang_zpowers hxB] at hLc0
  have hres := e6two_lang hR hR2 S₁ h.prime hp5 hq hc ⟨w, hρ⟩ (fr₁.DLang D) hDcard a ha hap hT
    i hΨ hr2 horth hspan hJc ⟨fr₁.toLang ⟨x, hxB⟩, hxD⟩ hx1 hLc0
    (fr₁.JLang_mono h.j_le_l)
  rcases hres with hcen | hlab
  ·
    have hDC : D ≤ Subgroup.centralizer (L : Set X) :=
      fr₁.le_centralizer_of_lang_commute h.d_le hLG hLq.1 hcen
    have hcyc : IsCyclic ↥D := h.l_cyc D hDC (IsPGroup.of_card h.d_card)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using h.b_elem.2 g (h.d_le g.2))
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rw [hord, h.d_card] at hdvd
    have hp2' := h.prime.two_le
    have := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  ·
    obtain ⟨e⟩ := fr₁.nonempty_equiv_JLang hLG hLq
    have hlabL : GGHasLabel ⟨LargeEvenLieTag.A, 5, f⟩ (↥L ⧸ Subgroup.center ↥L) :=
      ggHasLabel_of_mulEquiv e.symm hlab.2.2.1
    exact false_of_labelA5 ggLabelRigidInput_holds hp hc h.l_split hlabL hlab.1

end CFSG.StandardType.TableCRes

end
