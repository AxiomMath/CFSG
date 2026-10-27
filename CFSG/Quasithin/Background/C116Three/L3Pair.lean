module

public import CFSG.Quasithin.Background.C116Three.ModuleDefs
public import CFSG.Quasithin.EmptyFaithful.R3c23Core

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem l3_card_eq {L : Subgroup (MulAut V)} (hL : IsL32 L) : Nat.card ↥L = 168 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hK

theorem commV_le_of_piece {G : Subgroup (MulAut V)} {W C : Subgroup V} (h : B56Piece G W C) :
    commV G ≤ W := by
  rcases h with ⟨hW, -⟩ | ⟨hW, -⟩ | ⟨-, hc, -⟩
  · rw [hW]; exact le_sup_left
  · rw [hW]; exact le_sup_left
  · exact hc

private theorem fix_of_isPerfect {L : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥L)
    {C : Subgroup V} (hC : ∀ b ∈ L, ∀ c ∈ C, b c = c) {u : V} (hmem : ∀ b ∈ L, b u * u⁻¹ ∈ C) :
    ∀ b ∈ L, b u = u := by
  let f : ↥L →* V :=
    { toFun := fun b => (b : MulAut V) u * u⁻¹
      map_one' := by simp
      map_mul' := fun b b' => by
        have h1 : (b : MulAut V) ((b' : MulAut V) u * u⁻¹) = (b' : MulAut V) u * u⁻¹ :=
          hC b b.2 _ (hmem b' b'.2)
        rw [map_mul, map_inv] at h1
        have h2 : (b : MulAut V) ((b' : MulAut V) u) =
            (b' : MulAut V) u * u⁻¹ * (b : MulAut V) u := mul_inv_eq_iff_eq_mul.1 h1
        show ((b : MulAut V) * (b' : MulAut V)) u * u⁻¹ = _
        rw [MulAut.mul_apply, h2]
        ac_rfl }
  have hker : ∀ b : ↥L, f b = 1 := by
    intro b
    have : b ∈ commutator ↥L := by rw [hperf.commutator_eq_top]; trivial
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker f this)
  intro b hb
  have := hker ⟨b, hb⟩
  exact mul_inv_eq_one.1 this

theorem pairData_l3 {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hbot : G₁ ⊓ G₂ = ⊥)
    (hperf₁ : Group.IsPerfect ↥G₁) (hperf₂ : Group.IsPerfect ↥G₂)
    (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = fixV (G₁ ⊔ G₂))
    (hp₁ : B56Piece G₁ W₁ (fixV (G₁ ⊔ G₂))) (hp₂ : B56Piece G₂ W₂ (fixV (G₁ ⊔ G₂)))
    (hI₁ : XMod.IsInv ↥(G₁ ⊔ G₂) W₁) (hI₂ : XMod.IsInv ↥(G₁ ⊔ G₂) W₂) :
    PairData G₁ G₂ W₁ W₂ (fixV (G₁ ⊔ G₂)) := by
  have hmem₁ : ∀ w ∈ W₁, ∀ b ∈ G₂, b w * w⁻¹ ∈ fixV (G₁ ⊔ G₂) := by
    intro w hw b hb
    rw [← hinf]
    have h1 : b w * w⁻¹ ∈ W₁ :=
      W₁.mul_mem (hI₁ ⟨b, Subgroup.mem_sup_right hb⟩ w hw) (W₁.inv_mem hw)
    have h2 : b w * w⁻¹ ∈ W₂ := commV_le_of_piece hp₂ (Subgroup.subset_closure ⟨b, hb, w, rfl⟩)
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hmem₂ : ∀ w ∈ W₂, ∀ a ∈ G₁, a w * w⁻¹ ∈ fixV (G₁ ⊔ G₂) := by
    intro w hw a ha
    rw [← hinf]
    have h1 : a w * w⁻¹ ∈ W₂ :=
      W₂.mul_mem (hI₂ ⟨a, Subgroup.mem_sup_left ha⟩ w hw) (W₂.inv_mem hw)
    have h2 : a w * w⁻¹ ∈ W₁ := commV_le_of_piece hp₁ (Subgroup.subset_closure ⟨a, ha, w, rfl⟩)
    exact Subgroup.mem_inf.2 ⟨h2, h1⟩
  exact
    { comm := hcomm
      inf_eq_bot := hbot
      sup_eq_top := hsup
      inf_eq := hinf
      fix_C := fun g hg c hc => mem_fixV.1 hc g hg
      inv₁ := fun a ha w hw => hI₁ ⟨a, Subgroup.mem_sup_left ha⟩ w hw
      inv₂ := fun b hb w hw => hI₂ ⟨b, Subgroup.mem_sup_right hb⟩ w hw
      triv₁ := fun b hb w hw => fix_of_isPerfect hperf₂
        (fun b' hb' c hc => mem_fixV.1 hc b' (Subgroup.mem_sup_right hb')) (u := w)
        (fun b' hb' => hmem₁ w hw b' hb') b hb
      triv₂ := fun a ha w hw => fix_of_isPerfect hperf₁
        (fun a' ha' c hc => mem_fixV.1 hc a' (Subgroup.mem_sup_left ha')) (u := w)
        (fun a' ha' => hmem₂ w hw a' ha') a ha }

theorem projSub_isPGroup {G₁ G₂ Q : Subgroup (MulAut V)} (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hbot : G₁ ⊓ G₂ = ⊥) (hQ : IsPGroup 2 Q) : IsPGroup 2 (R3c23.projSub G₁ G₂ Q hcomm) := by
  intro g
  obtain ⟨hg, y, hy, hgy⟩ := R3c23.mem_projSub.1 g.2
  obtain ⟨k, hk⟩ := hQ ⟨g.1 * y, hgy⟩
  have hk' : (g.1 * y) ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hcom : Commute g.1 y := hcomm _ hg _ hy
  have hsplit : g.1 ^ 2 ^ k * y ^ 2 ^ k = 1 := by
    rw [← hcom.mul_pow]
    exact hk'
  have hmem1 : g.1 ^ 2 ^ k ∈ G₁ ⊓ G₂ := by
    refine Subgroup.mem_inf.2 ⟨G₁.pow_mem hg _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hsplit]
    exact G₂.inv_mem (G₂.pow_mem hy _)
  rw [hbot] at hmem1
  exact ⟨k, Subtype.ext (by simpa using Subgroup.mem_bot.1 hmem1)⟩

private theorem l3Pair_conj_apply (τ a : MulAut V) (v : V) :
    ((MulAut.conj τ).toMonoidHom a) v = τ (a (τ⁻¹ v)) := by
  simp [MulAut.conj_apply]

theorem commV_map_conj {G₁ G₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (h : G₂ = G₁.map (MulAut.conj τ).toMonoidHom) :
    (commV G₁).map τ.toMonoidHom = commV G₂ := by
  subst h
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨a, ha, v, rfl⟩
    show τ (a v * v⁻¹) ∈ commV _
    have : τ (a v * v⁻¹) = ((MulAut.conj τ).toMonoidHom a) (τ v) * (τ v)⁻¹ := by
      rw [l3Pair_conj_apply, map_mul, map_inv]
      simp
    rw [this]
    exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem _ ha, τ v, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨a (τ⁻¹ v) * (τ⁻¹ v)⁻¹, Subgroup.subset_closure ⟨a, ha, τ⁻¹ v, rfl⟩, ?_⟩
    show τ (a (τ⁻¹ v) * (τ⁻¹ v)⁻¹) = _
    rw [l3Pair_conj_apply, map_mul, map_inv]
    simp

theorem map_fixV_of_norm {J : Subgroup (MulAut V)} {τ : MulAut V} (h : ∀ l ∈ J, τ * l * τ⁻¹ ∈ J)
    (h' : ∀ l ∈ J, τ⁻¹ * l * τ ∈ J) : (fixV J).map τ.toMonoidHom = fixV J := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
    refine mem_fixV.2 (fun l hl => ?_)
    have h1 : (τ⁻¹ * l * τ) v = v := mem_fixV.1 hv _ (h' l hl)
    have h2 : τ⁻¹ (l (τ v)) = v := h1
    calc l (τ v) = τ (τ⁻¹ (l (τ v))) := (MulAut.apply_inv_self V τ _).symm
      _ = τ v := by rw [h2]
  · intro v hv
    refine Subgroup.mem_map.2 ⟨τ⁻¹ v, mem_fixV.2 (fun l hl => ?_), MulAut.apply_inv_self V τ v⟩
    have h1 : (τ * l * τ⁻¹) v = v := mem_fixV.1 hv _ (h l hl)
    have h2 : τ (l (τ⁻¹ v)) = v := h1
    calc l (τ⁻¹ v) = τ⁻¹ (τ (l (τ⁻¹ v))) := by simp
      _ = τ⁻¹ v := by rw [h2]

end CFSG.Quasithin.C116Three
