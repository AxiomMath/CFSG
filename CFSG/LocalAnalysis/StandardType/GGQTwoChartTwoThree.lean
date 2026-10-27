module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeBlk
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeOdd
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeSurj
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeFix
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeSym

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

private theorem qTwoChartTwoThree_mem_map_toEmbedding
    {I : Finset (Fin (n + 1))} {π : Equiv.Perm (Fin (n + 1))} {y : Fin (n + 1)} :
    y ∈ I.map π.toEmbedding ↔ π.symm y ∈ I := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    simpa using hx
  · intro hy
    exact ⟨π.symm y, hy, by simp⟩

private theorem qTwoChartTwoThree_mem_fixI_iff_supported
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) (b : ↥Bs) :
    (b : G) ∈ qTwoFixI ρA I ↔
      ∀ σ : Equiv.Perm (Fin (n + 1)), (∀ y, y ∉ I → σ y = y) →
        (((ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b) := by
  rw [qTwoChartTwoThree_mem_fixI_iff]
  constructor
  · intro h σ hσ
    exact h ⟨_, qTwoChartTwoThree_mem_symI.mpr ⟨σ, hσ, rfl⟩⟩
  · intro h s
    obtain ⟨σ, hσ, hσs⟩ := qTwoChartTwoThree_mem_symI.mp s.2
    rw [← hσs]
    exact h σ hσ

theorem qTwoChartTwoThree_fixI_conj
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) {π : Equiv.Perm (Fin (n + 1))} {g : G}
    (hg : ∀ b : ↥Bs,
      ((((ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : ↥Bs) : G) = g * (b : G) * g⁻¹) :
    qTwoFixI ρA (I.map π.toEmbedding) =
      (qTwoFixI ρA I).map (MulAut.conj g).toMonoidHom := by
  let ρA' : Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs :=
    (Subgroup.subtype (ggAutomizerJoin L Bs 𝒦)).comp ρA.toMonoidHom
  have hρA' : ∀ σ, ρA' σ =
      (((ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := fun σ => rfl
  ext x
  constructor
  · intro hx
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hx
    have hb₀' : (b₀ : G) ∈ qTwoFixI ρA (I.map π.toEmbedding) :=
      Subgroup.mem_map_of_mem _ hb₀
    let b₁ : ↥Bs := (ρA' π)⁻¹ b₀
    have hb₁app : ρA' π b₁ = b₀ := MulAut.apply_inv_self (↥Bs) (ρA' π) b₀
    have hb₁ : (b₁ : G) ∈ qTwoFixI ρA I := by
      rw [qTwoChartTwoThree_mem_fixI_iff_supported]
      intro σ hσ
      have hτ : ∀ y, y ∉ I.map π.toEmbedding → (π * σ * π⁻¹) y = y := by
        intro y hy
        have hy' : π.symm y ∉ I := by
          intro hmem
          exact hy ((qTwoChartTwoThree_mem_map_toEmbedding).mpr hmem)
        have hσy := hσ (π.symm y) hy'
        show π (σ (π.symm y)) = y
        rw [hσy, Equiv.apply_symm_apply]
      have hfix := (qTwoChartTwoThree_mem_fixI_iff_supported ρA (I.map π.toEmbedding) b₀).mp hb₀'
        (π * σ * π⁻¹) hτ
      have hconj : ρA' (π * σ * π⁻¹) = ρA' π * ρA' σ * (ρA' π)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      change (ρA' (π * σ * π⁻¹)) b₀ = b₀ at hfix
      rw [hconj] at hfix
      have hkey : ρA' σ b₁ = b₁ := by
        apply (ρA' π).injective
        have hfix' := hfix
        rw [MulAut.mul_apply, MulAut.mul_apply] at hfix'
        rw [← hb₁app, MulAut.inv_apply_self] at hfix'
        rw [hfix', hb₁app]
      simpa only [hρA' σ] using hkey
    have hg₁ : ((ρA' π b₁ : ↥Bs) : G) = g * (b₁ : G) * g⁻¹ := by
      change ((((ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b₁ : ↥Bs) : G) =
        g * (b₁ : G) * g⁻¹
      exact hg b₁
    have hval : (MulAut.conj g).toMonoidHom (b₁ : G) = (b₀ : G) := by
      change MulAut.conj g (b₁ : G) = (b₀ : G)
      rw [MulAut.conj_apply, ← hg₁, hb₁app]
    change (b₀ : G) ∈ (qTwoFixI ρA I).map (MulAut.conj g).toMonoidHom
    rw [← hval]
    exact Subgroup.mem_map_of_mem _ hb₁
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b₁, hb₁, rfl⟩ := Subgroup.mem_map.mp ha
    have hb₁fix : (b₁ : G) ∈ qTwoFixI ρA I := Subgroup.mem_map_of_mem _ hb₁
    let b₀ : ↥Bs := ρA' π b₁
    have hg₁ : ((ρA' π b₁ : ↥Bs) : G) = g * (b₁ : G) * g⁻¹ := by
      change ((((ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b₁ : ↥Bs) : G) =
        g * (b₁ : G) * g⁻¹
      exact hg b₁
    have hb₀val : (b₀ : G) = g * (b₁ : G) * g⁻¹ := by
      simpa only [b₀] using hg₁
    have hb₀ : (b₀ : G) ∈ qTwoFixI ρA (I.map π.toEmbedding) := by
      rw [qTwoChartTwoThree_mem_fixI_iff_supported]
      intro τ hτ
      let σ : Equiv.Perm (Fin (n + 1)) := π⁻¹ * τ * π
      have hσ : ∀ y, y ∉ I → σ y = y := by
        intro y hy
        have hπy : π y ∉ I.map π.toEmbedding := by
          intro hmem
          exact hy (by simpa using (qTwoChartTwoThree_mem_map_toEmbedding).mp hmem)
        have hτy := hτ (π y) hπy
        show π⁻¹ (τ (π y)) = y
        rw [Equiv.Perm.inv_def, hτy, Equiv.symm_apply_apply]
      have hfix := (qTwoChartTwoThree_mem_fixI_iff_supported ρA I b₁).mp hb₁fix σ hσ
      have hfix' : ρA' σ b₁ = b₁ := by
        simpa only [hρA' σ] using hfix
      have hmul : ρA' τ * ρA' π = ρA' π * ρA' σ := by
        rw [← map_mul, ← map_mul]
        congr 1
        show τ * π = π * σ
        rw [show σ = π⁻¹ * τ * π from rfl]
        group
      have hkey : ρA' τ b₀ = b₀ := by
        calc ρA' τ b₀ = (ρA' τ * ρA' π) b₁ := by
              simp only [b₀, MulAut.mul_apply]
          _ = (ρA' π * ρA' σ) b₁ := by rw [hmul]
          _ = ρA' π (ρA' σ b₁) := by rw [MulAut.mul_apply]
          _ = ρA' π b₁ := by rw [hfix']
          _ = b₀ := rfl
      simpa only [hρA' τ] using hkey
    have hval : (MulAut.conj g).toMonoidHom (b₁ : G) = (b₀ : G) := by
      change MulAut.conj g (b₁ : G) = (b₀ : G)
      rw [MulAut.conj_apply, hb₀val]
    change (MulAut.conj g).toMonoidHom (b₁ : G) ∈
      qTwoFixI ρA (I.map π.toEmbedding)
    rw [hval]
    exact hb₀

theorem qTwoChartTwoThree_map_inf_centralizer (g : G) (X F : Subgroup G) :
    (X ⊓ Subgroup.centralizer (F : Set G)).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.centralizer ((F.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro z ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hx w hw]
  · intro hy
    simp only [Subgroup.mem_centralizer_iff] at hy
    have hy' : (MulAut.conj g).toMonoidHom ((MulAut.conj g)⁻¹ y) = y := by
      change MulAut.conj g ((MulAut.conj g)⁻¹ y) = y
      rw [MulAut.apply_inv_self]
    refine ⟨(MulAut.conj g)⁻¹ y, ?_, hy'⟩
    intro w hw
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul]
    have hx : (MulAut.conj g) ((MulAut.conj g)⁻¹ y) = y :=
      MulAut.apply_inv_self G (MulAut.conj g) y
    rw [hx]
    exact hy ((MulAut.conj g) w) (Subgroup.mem_map_of_mem _ hw)

theorem qTwoChartTwoThree_oTwoPrime_map_conj (g : G) (X : Subgroup G) :
    qTwoOTwoPrime (X.map (MulAut.conj g).toMonoidHom) =
      (qTwoOTwoPrime X).map (MulAut.conj g).toMonoidHom := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [qTwoOTwoPrime, qTwoOTwoPrime, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, k, hk⟩
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨x, ⟨hxX, k, ?_⟩, rfl⟩
    apply hinj
    rw [map_pow, hk, map_one]
  · rintro ⟨x, ⟨hxX, k, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hxX, k, by rw [← map_pow, hk, map_one]⟩

section Chart

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

private theorem qTwoChartTwoThree_coordBlockSU_mono {T Q : Finset (Fin m)} (hTQ : T ⊆ Q) :
    coordBlockSU F0 2 1 T ≤ coordBlockSU F0 2 1 Q := by
  intro u hu
  rw [mem_coordBlockSU_iff] at hu ⊢
  intro i j hij
  exact hu i j (hij.imp (fun hi h => hi (hTQ h)) (fun hj h => hj (hTQ h)))

theorem qTwoChartTwoThree_two_elt_mem (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (hF0 : Nat.card F0 = 4) {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ)
    {ε0 : Fin m ↪ Fin (n + 1)} (hε0 : QTwoFrameMatch S ψ ε0)
    {T Q : Finset (Fin m)} (hTQ : T ⊆ Q) (hQ : Q.card = 4) {y : G}
    (hyQ : y ∈ (coordBlockSU F0 2 1 Q).map ψ)
    (hyC : y ∈ Subgroup.centralizer ((qTwoFixI S.ρA (T.map ε0) : Subgroup G) : Set G))
    {a : ℕ} (hy : y ^ (2 ^ a) = 1) : y ∈ (coordBlockSU F0 2 1 T).map ψ := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  haveI : Fintype F0ˣ := Fintype.ofFinite F0ˣ
  obtain ⟨u, huQ, hψu⟩ := Subgroup.mem_map.mp hyQ
  have hperm : ∀ σ : Equiv.Perm (Fin m), ∃ u : Su F0 2 1 m, ∀ i : Fin m,
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
        Pi.single (σ i) 1 := fun σ => (hε0 σ).imp fun u h => h.1
  have hcardu : Fintype.card F0ˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hF0]
  obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card (α := F0ˣ) (a := 1)
    (by rw [hcardu]; norm_num)
  have hm5 : 5 ≤ m := S.hm
  have hmlt : Q.card < (Finset.univ : Finset (Fin m)).card := by
    rw [hQ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hmlt
  have hpow : u ^ (2 ^ a) = 1 := by
    apply qTwoChartTwoThree_pow_eq_one_of_central hperm hi₀ huQ (2 ^ a)
    apply hψ.2.1
    rw [MonoidHom.mem_ker, map_pow, hψu, hy]
  have hcomm : ∀ k ∈ Q, k ∉ T →
      qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω) *
        (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag (Function.update (1 : Fin m → F0ˣ) k ω))⁻¹ =
        (u : GL (Fin m) F0) := by
    intro k hkQ hkT
    obtain ⟨b, hb⟩ := qTwoChartTwoThree_exists_induces S hF0 hψ
      (Function.update (1 : Fin m → F0ˣ) k ω)
    have hconst : ∀ i ∈ T, ∀ j ∈ T,
        Function.update (1 : Fin m → F0ˣ) k ω i =
          Function.update (1 : Fin m → F0ˣ) k ω j := by
      intro i hi j hj
      have hik : i ≠ k := by rintro rfl; exact hkT hi
      have hjk : j ≠ k := by rintro rfl; exact hkT hj
      rw [Function.update_apply, Function.update_apply, if_neg hik, if_neg hjk]
      rfl
    have hbF : (b : G) ∈ qTwoFixI S.ρA (T.map ε0) :=
      qTwoChartTwoThree_mem_fixI S hε0 hb hconst
    have hcent := Subgroup.mem_centralizer_iff.mp hyC (b : G) hbF
    obtain ⟨u', hu'mat, hu'ψ⟩ := hb u
    have hby : (b : G) * ψ u * (b : G)⁻¹ = ψ u := by
      rw [hψu]
      rw [hcent, mul_assoc, mul_inv_cancel, mul_one]
    have hψu' : ψ u' = ψ u := by
      rw [hu'ψ, hby]
    have hker : u' * u⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := by
      apply hψ.2.1
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψu', mul_inv_cancel]
    have hueq : u' = u := qTwoChartTwoThree_eq_of_central_quot hperm hi₀ huQ hu'mat hker
    rw [← hu'mat, hueq]
  have huT : u ∈ coordBlockSU F0 2 1 T :=
    qTwoChartTwoThree_mem_block hF0 hTQ hω huQ hcomm hpow
  rw [← hψu]
  exact Subgroup.mem_map_of_mem _ huT

theorem qTwoChartTwoThree_chart (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (hF0 : Nat.card F0 = 4) {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ)
    {ε0 : Fin m ↪ Fin (n + 1)} (hε0 : QTwoFrameMatch S ψ ε0)
    {T Q : Finset (Fin m)} (hTQ : T ⊆ Q) (hQ : Q.card = 4) (h2 : 2 ≤ T.card) (h3 : T.card ≤ 3) :
    (coordBlockSU F0 2 1 T).map ψ =
      qTwoOTwoPrime ((coordBlockSU F0 2 1 Q).map ψ ⊓
        Subgroup.centralizer ((qTwoFixI S.ρA (T.map ε0) : Subgroup G) : Set G)) := by
  apply le_antisymm
  · rw [← qTwoChartTwoThree_oTwoPrime_coordBlockSU hF0 h2 h3, qTwoOTwoPrime,
      MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨u, ⟨huT, k, hk⟩, rfl⟩
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, k, ?_⟩
    · exact Subgroup.mem_map_of_mem ψ (qTwoChartTwoThree_coordBlockSU_mono hTQ huT)
    · exact qTwoChartTwoThree_block_le_centralizer S hψ hε0 T
        (Subgroup.mem_map_of_mem ψ huT)
    · rw [← map_pow, hk, map_one]
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, a, hya⟩
    exact qTwoChartTwoThree_two_elt_mem S hF0 hψ hε0 hTQ hQ hy.1 hy.2 hya

private theorem qTwoChartTwoThree_blockOf_map (ψ : Su F0 2 1 m →* G) (g : G)
    (T : Finset (Fin m)) :
    qTwoBlockOf ψ g T =
      ((coordBlockSU F0 2 1 T).map ψ).map (MulAut.conj g).toMonoidHom := by
  rw [qTwoBlockOf]
  exact (Subgroup.map_map (coordBlockSU F0 2 1 T)
    (MulAut.conj g).toMonoidHom ψ).symm

theorem qTwoChart_twoThreeBlock (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0)
    {g : G} {π : Equiv.Perm (Fin (n + 1))}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    {J : Finset (Fin m)} (h2 : 2 ≤ J.card) (h3 : J.card ≤ 3)
    {Q : Finset (Fin m)} (hQ : Q.card = 4) (hJQ : J ⊆ Q) :
    qTwoBlockOf ψ g J = qTwoOTwoPrime
      (qTwoBlockOf ψ g Q ⊓
        Subgroup.centralizer ((qTwoFixI S.ρA (qTwoFrameSet ε0 π J) : Subgroup G) :
          Set G)) := by
  have hFj : qTwoFixI S.ρA (qTwoFrameSet ε0 π J) =
      (qTwoFixI S.ρA (J.map ε0)).map (MulAut.conj g).toMonoidHom :=
    qTwoChartTwoThree_fixI_conj S.ρA (J.map ε0) hg.2.2
  rw [qTwoChartTwoThree_blockOf_map ψ g J, qTwoChartTwoThree_blockOf_map ψ g Q, hFj,
    ← qTwoChartTwoThree_map_inf_centralizer g
      ((coordBlockSU F0 2 1 Q).map ψ) (qTwoFixI S.ρA (J.map ε0)),
    qTwoChartTwoThree_oTwoPrime_map_conj g
      (((coordBlockSU F0 2 1 Q).map ψ) ⊓
        Subgroup.centralizer ((qTwoFixI S.ρA (J.map ε0) : Subgroup G) : Set G)),
    qTwoChartTwoThree_chart S hF0 hψ hε0 hJQ hQ h2 h3]

end Chart

end CFSG.StandardType.QTwo

end
