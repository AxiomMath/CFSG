module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthTorus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Multiplicative CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] {L : Type} [Group L]

private theorem conj_inv_mem_centralizer {G : Type} [Group G] {b₀ c g : G}
    (hc : c ∈ Subgroup.centralizer ({b₀} : Set G))
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    g⁻¹ * c * g ∈ Subgroup.centralizer ({b₀} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hb : g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ :=
    (Subgroup.mem_normalizer_iff.mp hg b₀).mp (Subgroup.mem_zpowers b₀)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc' : Commute c b₀ := (Subgroup.mem_centralizer_iff.mp hc b₀ rfl).symm
  have hcomm : Commute c (g * b₀ * g⁻¹) := by
    rw [← hm]
    exact Commute.zpow_right hc' m
  have hconj : Commute (g⁻¹ * c * g) b₀ := by
    have h := Commute.conj hcomm g⁻¹
    have e1 : g⁻¹ * c * (g⁻¹)⁻¹ = g⁻¹ * c * g := by group
    have e2 : g⁻¹ * (g * b₀ * g⁻¹) * (g⁻¹)⁻¹ = b₀ := by group
    rwa [e1, e2] at h
  exact hconj.symm

private theorem map_conj_le_centralizer {G : Type} [Group G] {b₀ : G} {K : Subgroup G} {g : G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    K.map (MulAut.conj g : G →* G) ≤ Subgroup.centralizer ({b₀} : Set G) := by
  have hP : Subgroup.zpowers (g * b₀ * g⁻¹) = Subgroup.zpowers b₀ := by
    rw [← MulAut.conj_apply]
    change Subgroup.zpowers ((MulAut.conj g : G →* G) b₀) = Subgroup.zpowers b₀
    rw [← MonoidHom.map_zpowers (MulAut.conj g : G →* G) b₀,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]
  rintro x ⟨k, hk, rfl⟩
  have hkC := hKC hk
  have hxc : Commute (g * k * g⁻¹) (g * b₀ * g⁻¹) := by
    have h := Commute.conj ((Subgroup.mem_centralizer_iff.mp hkC b₀ rfl).symm) g
    simpa [MulAut.conj_apply] using h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hP.symm ▸ Subgroup.mem_zpowers b₀)
  have hcomm : Commute (g * k * g⁻¹) b₀ := by
    rw [← hm]
    exact Commute.zpow_right hxc m
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hcomm.symm

private theorem le_normalizer_map_conj {G : Type} [Group G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    {g : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    K ≤ Subgroup.normalizer (K.map (MulAut.conj g : G →* G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let c : ↥(Subgroup.centralizer ({b₀} : Set G)) :=
    ⟨g⁻¹ * k * g, conj_inv_mem_centralizer (hKC hk) hg⟩
  let y' : ↥(Subgroup.centralizer ({b₀} : Set G)) := ⟨y, hKC hy⟩
  have hmem : c * y' * c⁻¹ ∈ K.subgroupOf (Subgroup.centralizer ({b₀} : Set G)) :=
    hKn.conj_mem y' (Subgroup.mem_subgroupOf.mpr hy) c
  refine Subgroup.mem_map.mpr ⟨(c * y' * c⁻¹ : ↥(Subgroup.centralizer ({b₀} : Set G))).val,
    Subgroup.mem_subgroupOf.mp hmem, ?_⟩
  change g * ((g⁻¹ * k * g) * y * (g⁻¹ * k * g)⁻¹) * g⁻¹ = k * (g * y * g⁻¹) * k⁻¹
  group

private theorem le_centralizer_of_inf_eq_bot {G : Type} [Group G] {K K' : Subgroup G}
    (hinf : K ⊓ K' = ⊥) (hKK' : K ≤ Subgroup.normalizer (K' : Set G))
    (hK'K : K' ≤ Subgroup.normalizer (K : Set G)) :
    K' ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : k * (x * k⁻¹ * x⁻¹) ∈ K' := by
    have h' : k * x * k⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hKK' hk) x).mp hx
    simpa only [mul_assoc] using K'.mul_mem h' (K'.inv_mem hx)
  have h2 : x * k⁻¹ * x⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hK'K hx) k⁻¹).mp (K.inv_mem hk)
  have h3 : k * (x * k⁻¹ * x⁻¹) ∈ K := K.mul_mem hk h2
  have h4 : k * (x * k⁻¹ * x⁻¹) = 1 := by
    have hmem : k * (x * k⁻¹ * x⁻¹) ∈ K ⊓ K' := ⟨h3, h1⟩
    rw [hinf] at hmem
    exact Subgroup.mem_bot.mp hmem
  calc k * x = (k * (x * k⁻¹ * x⁻¹)) * (x * k) := by group
    _ = x * k := by rw [h4, one_mul]

private theorem exists_zmod_eq_pow_of_mem_zpowers {G : Type} [Group G] [Finite G] {b x : G}
    (hb : orderOf b = 3) (hx : x ∈ Subgroup.zpowers b) (hx1 : x ≠ 1) :
    ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧ x = b ^ s.val := by
  classical
  have hmem : x ∈ (Finset.range (orderOf b)).image (b ^ ·) := by
    rwa [← mem_zpowers_iff_mem_range_orderOf]
  rw [hb] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨r, hr, rfl⟩ := hmem
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact absurd (pow_zero b) hx1
  · exact ⟨1, Or.inl rfl, by simp [ZMod.val_one]⟩
  · exact ⟨-1, Or.inr rfl, by simp [ZMod.val_neg_one]⟩

theorem normalizer_zpowers_le_normalizer [Finite G] {b₀ : G} {K A : Subgroup G}
    (hKs : IsSimpleGroup ↥K) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hAK : A ≤ K) (hA3 : IsPGroup 3 A) (hAc : ¬ IsCyclic A) :
    Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hC
  set K' : Subgroup G := K.map (MulAut.conj g : G →* G) with hK'def
  have hK'C : K' ≤ C := hK'def ▸ map_conj_le_centralizer hKC hg
  have hKK' : K ≤ Subgroup.normalizer (K' : Set G) :=
    hK'def ▸ le_normalizer_map_conj hKC hKn hg
  have hCK : C ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hK'K : K' ≤ Subgroup.normalizer (K : Set G) := hK'C.trans hCK
  have hKnorm : K ≤ Subgroup.normalizer (K ⊓ K' : Subgroup G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    exact ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk),
      (Subgroup.le_normalizer_iff.mp hKK' k hk x hx.2)⟩
  haveI hHn : ((K ⊓ K').subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
  haveI : IsSimpleGroup ↥K := hKs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ K').subgroupOf K) with hbot | htop
  · have hdisj : K ⊓ K' = ⊥ := by
      have hd : Disjoint (K ⊓ K') K := Subgroup.subgroupOf_eq_bot.mp hbot
      have h := hd.eq_bot
      rwa [inf_of_le_left inf_le_left] at h
    have hK'le : K' ≤ Subgroup.centralizer (K : Set G) :=
      le_centralizer_of_inf_eq_bot hdisj hKK' hK'K
    have hA : A.map (MulAut.conj g : G →* G) ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.map_mono hAK).trans hK'le
    have hAcyc : IsCyclic (A.map (MulAut.conj g : G →* G)) :=
      hcyc _ hA (hA3.map (MulAut.conj g).toMonoidHom)
    exfalso
    exact hAc ((Subgroup.equivMapOfInjective A (MulAut.conj g : G →* G)
      (MulAut.conj g).injective).isCyclic.mpr hAcyc)
  · have hKle : K ≤ K ⊓ K' := Subgroup.subgroupOf_eq_top.mp htop
    have hKle' : K ≤ K' := fun x hx => (hKle hx).2
    have hcard : Nat.card ↥K' ≤ Nat.card ↥K := by
      rw [hK'def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hEq : K = K' := Subgroup.eq_of_le_of_card_ge hKle' hcard
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hK'def]
    exact hEq.symm

private abbrev torusImg {G L : Type} [Group G] [Group L] {n : ℕ} {K : Subgroup G}
    (φ : ↥K ≃* L) (τ : (Fin n → Multiplicative (ZMod 3)) →* L) : Subgroup G :=
  (τ.range).map (K.subtype.comp φ.symm.toMonoidHom)

private theorem torusImg_le {G L : Type} [Group G] [Group L] {n : ℕ} {K : Subgroup G}
    (φ : ↥K ≃* L) (τ : (Fin n → Multiplicative (ZMod 3)) →* L) :
    torusImg φ τ ≤ K := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  exact (φ.symm z).2

private theorem closure_mulSingle_eq_top (n : ℕ) :
    Subgroup.closure (Set.range fun i : Fin n =>
      (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3))) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [← Finset.univ_prod_mulSingle f]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hsingle : Pi.mulSingle i (f i) =
      (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ^ (toAdd (f i)).val := by
    rw [← Pi.mulSingle_pow]
    congr 1
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact (ofAdd_toAdd (f i)).symm
  have hmem : (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ∈
      Subgroup.closure (Set.range fun i : Fin n =>
        (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3))) :=
    Subgroup.subset_closure ⟨i, rfl⟩
  rw [hsingle]
  exact Subgroup.pow_mem _ hmem _

private theorem span_le_torusImg_sup {G L : Type} [Group G] [Group L] {n : ℕ} {b₀ : G}
    {K : Subgroup G} (φ : ↥K ≃* L) (τ : (Fin n → Multiplicative (ZMod 3)) →* L)
    (B : Basis3 G (n + 1)) (hb0 : B.b 0 = b₀)
    (hbsucc : ∀ i, B.b i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G)) :
    B.span ≤ torusImg φ τ ⊔ Subgroup.zpowers b₀ := by
  rw [Basis3.span, Subgroup.closure_le]
  rintro y ⟨j, rfl⟩
  cases j using Fin.cases with
  | zero =>
    rw [hb0]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)
  | succ i =>
    rw [hbsucc i]
    exact Subgroup.mem_sup_left
      (Subgroup.mem_map.mpr ⟨τ (Pi.mulSingle i (ofAdd 1)), ⟨Pi.mulSingle i (ofAdd 1), rfl⟩, rfl⟩)

private theorem zpowers_le_normalizer_torusImg {G L : Type} [Group G] [Group L] {n : ℕ}
    {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    (τ : (Fin n → Multiplicative (ZMod 3)) →* L)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) :
    Subgroup.zpowers b₀ ≤ Subgroup.normalizer (torusImg φ τ : Set G) := by
  rw [Subgroup.zpowers_le]
  refine (Subgroup.centralizer_le_normalizer (torusImg φ τ : Set G)) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hKC (torusImg_le φ τ hy)) b₀ rfl).symm

private theorem span_inf_le_torusImg {G L : Type} [Group G] [Group L] {n : ℕ} {b₀ : G}
    {K : Subgroup G} (φ : ↥K ≃* L) (τ : (Fin n → Multiplicative (ZMod 3)) →* L)
    (B : Basis3 G (n + 1)) (hb0 : B.b 0 = b₀)
    (hbsucc : ∀ i, B.b i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G))
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K) :
    B.span ⊓ K ≤ torusImg φ τ := by
  intro x hx
  have hsup : x ∈ torusImg φ τ ⊔ Subgroup.zpowers b₀ :=
    span_le_torusImg_sup φ τ B hb0 hbsucc hx.1
  have hPT := zpowers_le_normalizer_torusImg φ τ hKC
  have hxset : x ∈ ((torusImg φ τ ⊔ Subgroup.zpowers b₀ : Subgroup G) : Set G) := hsup
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (torusImg φ τ) (Subgroup.zpowers b₀) hPT,
    Set.mem_mul] at hxset
  obtain ⟨t, htT, p, hpP, hx'⟩ := hxset
  have hpK : p ∈ K := by
    have h1 : t⁻¹ * x ∈ K := K.mul_mem (K.inv_mem (torusImg_le φ τ htT)) hx.2
    rwa [← hx', inv_mul_cancel_left] at h1
  have hp1 : p = 1 := (Subgroup.disjoint_def.mp hdisj) hpP hpK
  rw [← hx', hp1, mul_one]
  exact htT

private theorem aut_mem_range {G L : Type} [Group G] [Group L] {n : ℕ} {b₀ : G}
    {K : Subgroup G} (φ : ↥K ≃* L) {τ : (Fin n → Multiplicative (ZMod 3)) →* L}
    (B : Basis3 G (n + 1)) (hb0 : B.b 0 = b₀)
    (hbsucc : ∀ i, B.b i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G))
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    {g : G} {β : MulAut ↥K} {α : MulAut L}
    (hβ : ∀ x : ↥K, (β x : G) = g * (x : G) * g⁻¹)
    (hαeq : ∀ f, α (τ f) = φ (β (φ.symm (τ f))))
    (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgB : g ∈ Subgroup.normalizer (B.span : Set G)) :
    ∀ f, α (τ f) ∈ τ.range := by
  have hgen_mem : ∀ i : Fin n, α (τ (Pi.mulSingle i (ofAdd 1))) ∈ τ.range := by
    intro i
    let x : ↥K := φ.symm (τ (Pi.mulSingle i (ofAdd 1)))
    have hxT : (x : G) ∈ torusImg φ τ :=
      Subgroup.mem_map.mpr ⟨τ (Pi.mulSingle i (ofAdd 1)), ⟨Pi.mulSingle i (ofAdd 1), rfl⟩, rfl⟩
    have hxspan : (x : G) ∈ B.span := by
      rw [show (x : G) = B.b i.succ from (hbsucc i).symm]
      exact B.b_mem_span i.succ
    have hyB : (β x : G) ∈ B.span := by
      rw [hβ x]
      exact (Subgroup.mem_normalizer_iff.mp hgB (x : G)).mp hxspan
    have hyK : (β x : G) ∈ K := by
      rw [hβ x]
      exact (Subgroup.mem_normalizer_iff.mp hgK (x : G)).mp (torusImg_le φ τ hxT)
    have hyT : (β x : G) ∈ torusImg φ τ :=
      span_inf_le_torusImg φ τ B hb0 hbsucc hKC hdisj ⟨hyB, hyK⟩
    obtain ⟨z, hz, hFz⟩ := Subgroup.mem_map.mp hyT
    have hφ : φ (β x) = z := by
      have hsub : β x = φ.symm z := Subtype.ext (by simpa using hFz.symm)
      rw [hsub]
      exact φ.apply_symm_apply z
    rw [hαeq, hφ]
    exact hz
  have hle : Subgroup.closure (Set.range fun i : Fin n =>
      (Pi.mulSingle i (ofAdd 1) : Fin n → Multiplicative (ZMod 3))) ≤
      (τ.range).comap (α.toMonoidHom.comp τ) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen_mem i
  intro f
  exact Subgroup.mem_comap.mp
    (hle (by rw [closure_mulSingle_eq_top]; exact Subgroup.mem_top f))

private theorem coord_conj_eq_single {L : Type} [Group L] {n : ℕ}
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} {α : MulAut L}
    (hαmem : ∀ f, α (τ f) ∈ τ.range)
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod 3}
    (hcoord : ∀ f f', α (τ f) = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    (i : Fin n) :
    α (τ (Pi.mulSingle i (ofAdd 1))) = τ (Pi.mulSingle (π i) (ofAdd (ε i))) := by
  let f : Fin n → Multiplicative (ZMod 3) := Pi.mulSingle i (ofAdd 1)
  obtain ⟨f', hf'⟩ := MonoidHom.mem_range.mp (hαmem f)
  have hco := hcoord f f' hf'.symm
  have hfi : f' (π i) = ofAdd (ε i) := by
    have h := hco i
    have h1 : toAdd (f i) = 1 := by simp [f]
    rw [h1, mul_one] at h
    simpa using congrArg ofAdd h
  have hf'ne : ∀ k, k ≠ π i → f' k = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := π.surjective k
    have hji : j ≠ i := fun h => hk (by rw [h])
    have h := hco j
    have h1 : toAdd (f j) = 0 := by simp [f, Pi.mulSingle_eq_of_ne hji]
    rw [h1, mul_zero] at h
    simpa using congrArg ofAdd h
  have hf'eq : f' = Pi.mulSingle (π i) (ofAdd (ε i)) := by
    funext k
    by_cases hk : k = π i
    · rw [hk, hfi, Pi.mulSingle_eq_same]
    · rw [hf'ne k hk, Pi.mulSingle_eq_of_ne hk]
  rw [← hf', hf'eq]

private theorem conj_b_succ_eq {G L : Type} [Group G] [Group L] {n : ℕ}
    {K : Subgroup G} (φ : ↥K ≃* L) {τ : (Fin n → Multiplicative (ZMod 3)) →* L}
    (B : Basis3 G (n + 1))
    (hbsucc : ∀ i, B.b i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G))
    {g : G} {β : MulAut ↥K} {α : MulAut L}
    (hβ : ∀ x : ↥K, (β x : G) = g * (x : G) * g⁻¹)
    (hαeq : ∀ f, α (τ f) = φ (β (φ.symm (τ f))))
    (hαmem : ∀ f, α (τ f) ∈ τ.range)
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod 3}
    (hcoord : ∀ f f', α (τ f) = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    (i : Fin n) :
    g * B.b i.succ * g⁻¹ = B.b ((π i).succ) ^ (ε i).val := by
  let f : Fin n → Multiplicative (ZMod 3) := Pi.mulSingle i (ofAdd 1)
  have hL : α (τ f) = τ (Pi.mulSingle (π i) (ofAdd (ε i))) :=
    coord_conj_eq_single hαmem hcoord i
  let x : ↥K := φ.symm (τ f)
  have hleft : (φ.symm (α (τ f)) : G) = g * B.b i.succ * g⁻¹ := by
    have hone : φ.symm (α (τ f)) = β x := by
      rw [hαeq f, MulEquiv.symm_apply_apply]
    rw [hone, hβ x, show (x : G) = B.b i.succ from (hbsucc i).symm]
  have hright : (φ.symm (τ (Pi.mulSingle (π i) (ofAdd (ε i)))) : G) =
      B.b ((π i).succ) ^ (ε i).val := by
    have hsingle : Pi.mulSingle (π i) (ofAdd (ε i)) =
        (Pi.mulSingle (π i) (ofAdd 1) : Fin n → Multiplicative (ZMod 3)) ^ (ε i).val := by
      rw [← Pi.mulSingle_pow]
      congr 1
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [hsingle, map_pow, map_pow, SubgroupClass.coe_pow, hbsucc]
  calc g * B.b i.succ * g⁻¹ = (φ.symm (α (τ f)) : G) := hleft.symm
    _ = (φ.symm (τ (Pi.mulSingle (π i) (ofAdd (ε i)))) : G) := by
      exact congrArg (fun z : L => (φ.symm z : G)) hL
    _ = B.b ((π i).succ) ^ (ε i).val := hright

private theorem mem_monoN0_of_acts {G : Type} [Group G] {n : ℕ} {b₀ : G}
    (B : Basis3 G (n + 1)) (hb0 : B.b 0 = b₀)
    {g : G} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hActs : B.Acts g M)
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod 3} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsucc : ∀ i, g * B.b i.succ * g⁻¹ = B.b ((π i).succ) ^ (ε i).val)
    {s₀ : ZMod 3} (hs₀ : s₀ = 1 ∨ s₀ = -1) (hx : g * b₀ * g⁻¹ = b₀ ^ s₀.val) :
    M ∈ monoN0 n := by
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), π)
  let s : Fin (n + 1) → ZMod 3 := Fin.cons s₀ ε
  have hσ0 : σ 0 = 0 := by
    change Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), π) 0 = 0
    exact Equiv.Perm.decomposeFin_symm_apply_zero _ _
  have hσsucc : ∀ i : Fin n, σ i.succ = (π i).succ := by
    intro i
    change Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), π) i.succ = (π i).succ
    rw [Equiv.Perm.decomposeFin_symm_apply_succ]
    simp
  have hs0 : s 0 = s₀ := rfl
  have hssucc : ∀ i : Fin n, s i.succ = ε i := fun _ => rfl
  have hsign : IsSign s := by
    intro j
    cases j using Fin.cases with
    | zero => rw [hs0]; exact hs₀
    | succ i => rw [hssucc i]; exact hε i
  have hacts : B.Acts g (spMat σ s) := by
    refine B.acts_spMat_iff.mpr fun j => ?_
    cases j using Fin.cases with
    | zero =>
      rw [hσ0, hs0, hb0]
      exact hx
    | succ i =>
      rw [hσsucc i, hssucc i]
      exact hsucc i
  exact ⟨σ, s, hsign, hσ0, B.acts_unique hActs hacts⟩

theorem torusBasis_hmono [Finite G] {n : ℕ} {b₀ : G} {K : Subgroup G} (φ : ↥K ≃* L)
    {τ : (Fin n → Multiplicative (ZMod 3)) →* L} (hτ : Function.Injective τ)
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    (hKN : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hnorm : ∀ α : MulAut L, (∀ f, α (τ f) ∈ τ.range) →
      ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', α (τ f) = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) :
    (torusBasis φ hτ hb₀ hKC hdisj).realized
      (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n := by
  classical
  intro M hM
  obtain ⟨g, hgN, hActs⟩ := hM
  let B : Basis3 G (n + 1) := torusBasis φ hτ hb₀ hKC hdisj
  have hActsB : B.Acts g M := hActs
  have hb0 : B.b 0 = b₀ := rfl
  have hbsucc : ∀ i, B.b i.succ = (φ.symm (τ (Pi.mulSingle i (ofAdd 1))) : G) := fun _ => rfl
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := hKN hgN
  have hgB : g ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hActsB
  let β : MulAut ↥K := K.normalizerMonoidHom ⟨g, hgK⟩
  have hβ : ∀ x : ↥K, (β x : G) = g * (x : G) * g⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨g, hgK⟩ x
  let α : MulAut L := φ.symm.trans (β.trans φ)
  have hαeq : ∀ f, α (τ f) = φ (β (φ.symm (τ f))) := fun _ => rfl
  have hαmem : ∀ f, α (τ f) ∈ τ.range :=
    aut_mem_range φ B hb0 hbsucc hKC hdisj hβ hαeq hgK hgB
  obtain ⟨π, ε, hε, hcoord⟩ := hnorm α hαmem
  have hsucc : ∀ i, g * B.b i.succ * g⁻¹ = B.b ((π i).succ) ^ (ε i).val := fun i =>
    conj_b_succ_eq φ B hbsucc hβ hαeq hαmem hcoord i
  have hx0mem : g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ :=
    (Subgroup.mem_normalizer_iff.mp hgN b₀).mp (Subgroup.mem_zpowers b₀)
  have hx0ne : g * b₀ * g⁻¹ ≠ 1 := by
    intro h1
    have h2 : orderOf (g * b₀ * g⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hb₀]
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨s₀, hs₀, hx₀⟩ := exists_zmod_eq_pow_of_mem_zpowers hb₀ hx0mem hx0ne
  exact mem_monoN0_of_acts B hb0 hActsB hε hsucc hs₀ hx₀

end CFSG.StandardType.FrameRoute.FS81
