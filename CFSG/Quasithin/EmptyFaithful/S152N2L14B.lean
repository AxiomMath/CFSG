module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.EmptyFaithful.S152N2Lin

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.QuasithinUnique

section OmegaOne

variable {G : Type*} [Group G]

theorem omegaOneCenter_eq_of_relIndex_two [Finite G] {T S ZS : Subgroup G}
    (hST : S ≤ T) (hidx : S.relIndex T = 2) (hZS : ZS ≤ S) (hZS2 : ∀ z ∈ ZS, z * z = 1)
    (hZSc : ∀ s ∈ S, ∀ z ∈ ZS, s * z = z * s) (hZ : Nat.card (omegaOneCenterOf T) = 2)
    (hZS4 : Nat.card ZS = 4) : ZS = omegaOneCenterOf S := by
  set Z₀ := omegaOneCenterOf S with hZ₀
  have hZSle : ZS ≤ Z₀ := by
    intro z hz
    refine Subgroup.subset_closure ⟨⟨hZS hz, Subgroup.mem_centralizer_iff.mpr fun s hs =>
      hZSc s hs z hz⟩, ?_⟩
    rw [sq]; exact hZS2 z hz
  have hZ₀prop : ∀ z ∈ Z₀, z ∈ S ∧ (∀ s ∈ S, s * z = z * s) ∧ z * z = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨hxS, hxc⟩, hx2⟩ := hx
      exact ⟨hxS, fun s hs => (Subgroup.mem_centralizer_iff.mp hxc s hs), by rwa [sq] at hx2⟩
    | one => exact ⟨S.one_mem, fun s _ => by simp, by simp⟩
    | mul a b _ _ ha hb =>
      refine ⟨S.mul_mem ha.1 hb.1, fun s hs => ?_, ?_⟩
      · rw [← mul_assoc, ha.2.1 s hs, mul_assoc, hb.2.1 s hs, ← mul_assoc]
      · have hab : a * b = b * a := hb.2.1 a ha.1
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2.2, hb.2.2, one_mul]
    | inv a _ ha =>
      refine ⟨S.inv_mem ha.1, fun s hs => ?_, ?_⟩
      · have := ha.2.1 s hs
        calc s * a⁻¹ = a⁻¹ * (a * s) * a⁻¹ := by group
          _ = a⁻¹ * (s * a) * a⁻¹ := by rw [this]
          _ = a⁻¹ * s := by group
      · have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2.2
        rw [ha', ha.2.2]
  have hZ₀ab : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a := fun a ha b hb =>
    ((hZ₀prop a ha).2.1 b (hZ₀prop b hb).1).symm
  have hSnormal : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  have hSn : ∀ τ ∈ T, ∀ s ∈ S, τ * s * τ⁻¹ ∈ S := fun τ hτ s hs =>
    hSnormal.conj_mem ⟨s, hST hs⟩ (Subgroup.mem_subgroupOf.mpr hs) ⟨τ, hτ⟩
  have hinv : ∀ τ ∈ T, ∀ z ∈ Z₀, τ * z * τ⁻¹ ∈ Z₀ := by
    intro τ hτ z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨hxS, hxc⟩, hx2⟩ := hx
      refine Subgroup.subset_closure ⟨⟨hSn τ hτ x hxS, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩,
        ?_⟩
      · have hs' : τ⁻¹ * s * τ ∈ S := by
          simpa using hSn τ⁻¹ (T.inv_mem hτ) s hs
        have h1 := Subgroup.mem_centralizer_iff.mp hxc _ hs'
        calc s * (τ * x * τ⁻¹) = τ * ((τ⁻¹ * s * τ) * x) * τ⁻¹ := by group
          _ = τ * (x * (τ⁻¹ * s * τ)) * τ⁻¹ := by rw [h1]
          _ = (τ * x * τ⁻¹) * s := by group
      · calc (τ * x * τ⁻¹) ^ 2 = τ * x ^ 2 * τ⁻¹ := by rw [pow_two, pow_two]; group
          _ = 1 := by rw [hx2]; group
    | one => simp
    | mul a b _ _ ha hb =>
      have : τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
      rw [this]; exact Z₀.mul_mem ha hb
    | inv a _ ha =>
      have : τ * a⁻¹ * τ⁻¹ = (τ * a * τ⁻¹)⁻¹ := by group
      rw [this]; exact Z₀.inv_mem ha
  obtain ⟨τ, hτT, hτS, hdec⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hidx
  have hττ : τ * τ ∈ S := (hdec τ hτT).resolve_right hτS
  have hττc : ∀ z ∈ Z₀, (τ * τ) * z = z * (τ * τ) := fun z hz => (hZ₀prop z hz).2.1 _ hττ
  have hmem : ∀ z : ↥Z₀, τ * z * τ⁻¹ * (z : G)⁻¹ ∈ Z₀ := fun z =>
    Z₀.mul_mem (hinv τ hτT z z.2) (Z₀.inv_mem z.2)
  let f : ↥Z₀ →* ↥Z₀ :=
    { toFun := fun z => ⟨τ * z * τ⁻¹ * (z : G)⁻¹, hmem z⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro z z'
        apply Subtype.ext
        show τ * ((z : G) * z') * τ⁻¹ * ((z : G) * z')⁻¹ =
          (τ * z * τ⁻¹ * (z : G)⁻¹) * (τ * z' * τ⁻¹ * (z' : G)⁻¹)
        have hc : (z : G)⁻¹ * (τ * z' * τ⁻¹ * (z' : G)⁻¹) =
            (τ * z' * τ⁻¹ * (z' : G)⁻¹) * (z : G)⁻¹ :=
          hZ₀ab _ (Z₀.inv_mem z.2) _ (hmem z')
        calc τ * ((z : G) * z') * τ⁻¹ * ((z : G) * z')⁻¹
            = (τ * z * τ⁻¹) * (τ * z' * τ⁻¹ * (z' : G)⁻¹ * (z : G)⁻¹) := by group
          _ = (τ * z * τ⁻¹) * ((z : G)⁻¹ * (τ * z' * τ⁻¹ * (z' : G)⁻¹)) := by rw [← hc]
          _ = _ := by group }
  have hfapp : ∀ z : ↥Z₀, ((f z : ↥Z₀) : G) = τ * z * τ⁻¹ * (z : G)⁻¹ := fun z => rfl
  have hrk : f.range ≤ f.ker := by
    rintro _ ⟨z, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    set y : G := τ * z * τ⁻¹ * (z : G)⁻¹ with hy
    have hyZ : y ∈ Z₀ := hmem z
    have hy2 : y * y = 1 := (hZ₀prop y hyZ).2.2
    have h1 : τ * y * τ⁻¹ = y⁻¹ := by
      calc τ * y * τ⁻¹ = (τ * τ) * (z : G) * τ⁻¹ * (z : G)⁻¹ * τ⁻¹ := by rw [hy]; group
        _ = (z : G) * (τ * τ) * τ⁻¹ * (z : G)⁻¹ * τ⁻¹ := by rw [hττc z z.2]
        _ = y⁻¹ := by rw [hy]; group
    show τ * y * τ⁻¹ * y⁻¹ = 1
    rw [h1, ← mul_inv_rev, hy2, inv_one]
  have hkerZ : ∀ z : f.ker, ((z.1 : ↥Z₀) : G) ∈ omegaOneCenterOf T := by
    intro z
    have hzZ : ((z.1 : ↥Z₀) : G) ∈ Z₀ := z.1.2
    have hzf : τ * ((z.1 : ↥Z₀) : G) * τ⁻¹ * ((z.1 : ↥Z₀) : G)⁻¹ = 1 := by
      have h0 : f z.1 = 1 := MonoidHom.mem_ker.mp z.2
      have h1 := congrArg Subtype.val h0
      rwa [hfapp] at h1
    have hτz : τ * ((z.1 : ↥Z₀) : G) = ((z.1 : ↥Z₀) : G) * τ := by
      have := congrArg (· * τ) hzf
      simp only [one_mul] at this
      calc τ * ((z.1 : ↥Z₀) : G) = τ * (z.1 : G) * τ⁻¹ * (z.1 : G)⁻¹ * ((z.1 : G) * τ) := by group
        _ = ((z.1 : ↥Z₀) : G) * τ := by rw [hzf, one_mul]
    refine Subgroup.subset_closure ⟨⟨hST (hZ₀prop _ hzZ).1,
      Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, ?_⟩
    · rcases hdec t ht with htτ | htS
      · have h1 := (hZ₀prop _ hzZ).2.1 (t * τ) htτ
        have h2 : t * ((z.1 : ↥Z₀) : G) * τ = ((z.1 : ↥Z₀) : G) * t * τ := by
          calc t * ((z.1 : ↥Z₀) : G) * τ = t * (((z.1 : ↥Z₀) : G) * τ) := by group
            _ = t * (τ * ((z.1 : ↥Z₀) : G)) := by rw [hτz]
            _ = (t * τ) * ((z.1 : ↥Z₀) : G) := by group
            _ = ((z.1 : ↥Z₀) : G) * (t * τ) := h1
            _ = ((z.1 : ↥Z₀) : G) * t * τ := by group
        exact mul_right_cancel h2
      · exact (hZ₀prop _ hzZ).2.1 t htS
    · rw [sq]; exact (hZ₀prop _ hzZ).2.2
  have hker : Nat.card f.ker ≤ 2 := by
    have hinj : Function.Injective
        (fun z : f.ker => (⟨((z.1 : ↥Z₀) : G), hkerZ z⟩ : ↥(omegaOneCenterOf T))) := by
      intro z z' h
      have h1 : ((z.1 : ↥Z₀) : G) = ((z'.1 : ↥Z₀) : G) := by simpa using h
      exact Subtype.ext (Subtype.ext h1)
    calc Nat.card f.ker ≤ Nat.card ↥(omegaOneCenterOf T) := Nat.card_le_card_of_injective _ hinj
      _ = 2 := hZ
  have hcard := Subgroup.card_ker_mul_card_range f
  have hle := Subgroup.card_le_of_le hrk
  have hZ0le : Nat.card Z₀ ≤ 4 := by
    calc Nat.card Z₀ = Nat.card f.ker * Nat.card f.range := hcard.symm
      _ ≤ Nat.card f.ker * Nat.card f.ker := Nat.mul_le_mul_left _ hle
      _ ≤ 2 * 2 := Nat.mul_le_mul hker hker
  exact Subgroup.eq_of_le_of_card_ge hZSle (by rw [hZS4]; exact hZ0le)

end OmegaOne

section Cyclic

variable {V : Type*} [CommGroup V]

theorem inv_eq_self_of_exp_two (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v := by
  have := hV v
  rw [pow_two, mul_eq_one_iff_eq_inv] at this
  exact this.symm

theorem commHom_commHom (hV : ∀ v : V, v ^ 2 = 1) (c : MulAut V) (v : V) :
    commHom c (commHom c v) = commHom (c * c) v := by
  simp only [commHom_apply, MulAut.mul_apply, map_mul, inv_eq_self_of_exp_two hV]
  have h1 : c v * c v = 1 := by rw [← pow_two]; exact hV _
  calc c (c v) * c v * (c v * v) = c (c v) * (c v * c v) * v := by ac_rfl
    _ = c (c v) * v := by rw [h1]; simp

theorem not_centralizes_fixV_sq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {c : MulAut V} (hc4 : c ^ 4 = 1) (hc2 : c ^ 2 ≠ 1)
    (hW : Nat.card (fixV (Subgroup.zpowers (c ^ 2))) = 4) :
    ¬ ∀ w ∈ fixV (Subgroup.zpowers (c ^ 2)), c w = w := by
  intro hcen
  have hcc : c * c = c ^ 2 := (pow_two c).symm
  have hb2 : (c ^ 2) * (c ^ 2) = 1 := by rw [← pow_add]; exact hc4
  have hcommcard : Nat.card (commV (Subgroup.zpowers (c ^ 2))) = 4 := by
    have h := card_fixV_mul_card_commV hb2
    rw [hcard, hW] at h
    omega
  have hfc : fixV (Subgroup.zpowers (c ^ 2)) = commV (Subgroup.zpowers (c ^ 2)) :=
    fixV_eq_commV_of_card hV hb2 hcard hcommcard
  have hker : (commHom c).ker = fixV (Subgroup.zpowers (c ^ 2)) := by
    rw [ker_commHom]
    ext v
    rw [mem_fixV_zpowers_iff, mem_fixV_zpowers_iff]
    constructor
    · intro h
      have : (c ^ 2) v = c (c v) := by rw [pow_two, MulAut.mul_apply]
      rw [this, h, h]
    · intro h
      exact hcen v ((mem_fixV_zpowers_iff).mpr h)
  have hkc : Nat.card (commHom c).ker = 4 := by rw [hker]; exact hW
  have hrc : Nat.card (commHom c).range = 4 := by
    have := Subgroup.card_ker_mul_card_range (commHom c)
    rw [hcard, hkc] at this
    omega
  have hrψ : Nat.card (commHom (c ^ 2)).range = 4 := by
    rw [range_commHom_eq_commV hb2]; exact hcommcard
  have hψφ : ∀ v, commHom (c ^ 2) v = commHom c (commHom c v) := fun v => by
    rw [commHom_commHom hV c v, hcc]
  have hle : (commHom (c ^ 2)).range ≤ (commHom c).range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨commHom c v, (hψφ v).symm⟩
  have heq : (commHom (c ^ 2)).range = (commHom c).range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrψ, hrc])
  have hrk : (commHom c).range = (commHom c).ker :=
    calc (commHom c).range = (commHom (c ^ 2)).range := heq.symm
      _ = commV (Subgroup.zpowers (c ^ 2)) := range_commHom_eq_commV hb2
      _ = fixV (Subgroup.zpowers (c ^ 2)) := hfc.symm
      _ = (commHom c).ker := hker.symm
  have hall : ∀ v, (c ^ 2) v = v := by
    intro v
    have h1 : commHom c v ∈ (commHom c).ker := hrk ▸ ⟨v, rfl⟩
    have h2 : commHom c (commHom c v) = 1 := h1
    have h3 : commHom (c ^ 2) v = 1 := by rw [hψφ]; exact h2
    rw [commHom_apply, mul_inv_eq_one] at h3
    exact h3
  exact hc2 (MulEquiv.ext fun v => by rw [hall v]; rfl)

end Cyclic

end S152N2

end CFSG.Quasithin
