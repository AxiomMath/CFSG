module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixInner
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispE
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGUSixTwoElemAbelian

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_coord_eq_zero_of_cent (hK : Nat.card K = 4) {L Bs : Subgroup G}
    {Q : Type} [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G}
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {s : ↥Bs}
    (hs₁ : (s : G) ∈ Subgroup.centralizer (J₁ : Set G))
    (hs₂ : (s : G) ∈
      Subgroup.centralizer ((J₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ∀ k : Fin 6, k ≠ c → βL (Additive.ofMul s) k = 0 := by
  classical
  have hyBs : g⁻¹ * (s : G) * g ∈ Bs := ((Subgroup.mem_normalizer_iff''.mp hgN) s).mp s.2
  have hyc : g⁻¹ * (s : G) * g ∈ Subgroup.centralizer (J₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hgh : g * h * g⁻¹ ∈ J₁.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hs₂) (g * h * g⁻¹) hgh
    calc h * (g⁻¹ * s * g) = g⁻¹ * ((g * h * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * h * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * s * g) * h := by group
  have hconst_s := ggQTwoDUnitSix_const_of_mem_centralizer hK hD hψk hω hind hJ₁ hs₁
  have hconst_y := ggQTwoDUnitSix_const_of_mem_centralizer hK hD hψk hω hind hJ₁
    (s := ⟨_, hyBs⟩) hyc
  have hαy : α ⟨_, hyBs⟩ = s := by
    apply Subtype.ext
    rw [hg]
    show g * (g⁻¹ * (s : G) * g) * g⁻¹ = s
    group
  have hdS : dSign 6 a c (βL (Additive.ofMul (⟨_, hyBs⟩ : ↥Bs))) = βL (Additive.ofMul s) := by
    rw [← hα, hαy]
  obtain ⟨k, hk⟩ : ∃ k, k ∈ (Finset.univ.erase c).erase a :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩),
        Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      norm_num)
  have hka : k ≠ a := (Finset.mem_erase.mp hk).1
  have hkS : k ∈ Finset.univ.erase c := (Finset.mem_erase.mp hk).2
  have hkc : k ≠ c := (Finset.mem_erase.mp hkS).1
  have haS : a ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩
  have hsk := congrFun hdS k
  rw [dSign_apply_vec, if_neg (not_or.mpr ⟨hka, hkc⟩)] at hsk
  have hsa := congrFun hdS a
  rw [dSign_apply_vec, if_pos (Or.inl rfl), hconst_y a haS k hkS, hsk,
    ← hconst_s a haS k hkS] at hsa
  have ht : βL (Additive.ofMul s) a = 0 :=
    (by decide : ∀ t : ZMod 3, -t = t → t = 0) _ hsa
  intro j hj
  rw [hconst_s j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) a haS, ht]

theorem ggQTwoDUnitSix_cent_E (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G}
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {s : ↥Bs}
    (hsc : βL (Additive.ofMul s) c = 0) (hs₁ : (s : G) ∈ Subgroup.centralizer (J₁ : Set G))
    (hs₂ : (s : G) ∈
      Subgroup.centralizer ((J₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    s = 1 := by
  have h0 := ggQTwoDUnitSix_coord_eq_zero_of_cent hK hD hψk hω hind hac hJ₁ hα hgN hg hs₁ hs₂
  have hβ : βL (Additive.ofMul s) = βL 0 := by
    rw [map_zero]
    funext j
    by_cases hj : j = c
    · subst hj
      exact hsc
    · exact h0 j hj
  have h1 : Additive.ofMul s = 0 := βL.injective hβ
  simpa using h1

theorem ggQTwoDUnitSix_not_unitary (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    (hBsE : IsElemAbelian 3 Bs) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {N : Subgroup G} (hJ₁N : J₁ ≤ N)
    (hJ₂N : J₁.map (MulAut.conj g).toMonoidHom ≤ N)
    (hlab : GGHasLabel ⟨.twA, 5, 1⟩ (↥N ⧸ Subgroup.center ↥N)) : False := by
  obtain ⟨A, hA, hAcard⟩ := qtwoDB24_image_of (m := 6) hBsE (βL := βL) (c := c) (N := N)
    (fun s hs => sup_le hJ₁N hJ₂N
      (ggQTwoDUnitSix_torus hK hD hψk hε hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hg s hs))
    (fun s hs hsC => ggQTwoDUnitSix_cent_E hK hD hψk hω hind hac hJ₁ hα hgN hg hs
      (Subgroup.centralizer_le hJ₁N hsC) (Subgroup.centralizer_le hJ₂N hsC))
  obtain ⟨K', _, _, hK', ⟨θ⟩⟩ := hlab
  have hA' : IsElemAbelian 3 (A.map θ.toMonoidHom) := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := u
      obtain ⟨_, ⟨b', hb', rfl⟩⟩ := v
      have hc := congrArg Subtype.val (hA.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      apply Subtype.ext
      show θ a' * θ b' = θ b' * θ a'
      rw [← map_mul, ← map_mul]
      exact congrArg θ hc
    · obtain ⟨a', ha', rfl⟩ := hy
      show θ a' ^ 3 = 1
      rw [← map_pow, hA.2 a' ha', map_one]
  have h := USixTwo.card_le_of_isElemAbelian (K := K') (by rw [hK']; norm_num) hA'
  rw [Subgroup.card_map_of_injective θ.injective, hAcard] at h
  norm_num at h

end CFSG.StandardType.QTwo

end
