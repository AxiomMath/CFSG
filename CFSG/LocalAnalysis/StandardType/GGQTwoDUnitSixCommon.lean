module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixComp
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteA
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggQTwoDUnitSix_coordBlockSU_mono {n : ℕ} {S T : Finset (Fin n)} (hST : S ⊆ T) :
    coordBlockSU K 2 1 S ≤ coordBlockSU K 2 1 T := by
  intro g hg
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro i j hij
  exact hg i j (hij.imp (fun h hi => h (hST hi)) (fun h hj => h (hST hj)))

theorem ggQTwoDUnitSix_coordBlockSU_erase_inf {n : ℕ} (a c : Fin n) :
    coordBlockSU K 2 1 (Finset.univ.erase c) ⊓ coordBlockSU K 2 1 (Finset.univ.erase a) =
      coordBlockSU K 2 1 ((Finset.univ.erase c).erase a) := by
  ext g
  rw [Subgroup.mem_inf, mem_coordBlockSU_iff, mem_coordBlockSU_iff, mem_coordBlockSU_iff]
  constructor
  · rintro ⟨hc, ha⟩ i j hij
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at hij
    by_cases hi : i = c
    · exact hc i j (Or.inl (by simp [hi]))
    by_cases hj : j = c
    · exact hc i j (Or.inr (by simp [hj]))
    rcases hij with h | h
    · have hia : i = a := by
        by_contra hne
        exact hi (h hne)
      exact ha i j (Or.inl (by simp [hia]))
    · have hja : j = a := by
        by_contra hne
        exact hj (h hne)
      exact ha i j (Or.inr (by simp [hja]))
  · intro h
    refine ⟨fun i j hij => h i j ?_, fun i j hij => h i j ?_⟩
    · rcases hij with hi | hj
      · exact Or.inl fun hR => hi (Finset.mem_erase.mp hR).2
      · exact Or.inr fun hR => hj (Finset.mem_erase.mp hR).2
    · rcases hij with hi | hj
      · exact Or.inl fun hR => hi (by simp [(Finset.mem_erase.mp hR).1])
      · exact Or.inr fun hR => hj (by simp [(Finset.mem_erase.mp hR).1])

theorem ggQTwoDUnitSix_eq_one_of_mem_center_su (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n)
    (hn3 : ¬ 3 ∣ n) {z : Su K 2 1 n} (hz : z ∈ Subgroup.center (Su K 2 1 n)) : z = 1 := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K) (p := 2)
      (f := 1) hK') hn hz
  have hdet : (u : K) ^ n = 1 := by
    have h1 : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := (mem_SUid.mp z.2).1
    rw [hu, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    exact h1
  have hu3 : u ^ 3 = 1 := by
    have hcard : Nat.card Kˣ = 3 := by
      have := Fintype.ofFinite K
      rw [Nat.card_units, hK]
    rw [← hcard]
    exact pow_card_eq_one'
  have hun : u ^ n = 1 := Units.ext (by simpa using hdet)
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3
  have hu1 : u = 1 := by
    have h : u ^ Nat.gcd 3 n = 1 := pow_gcd_eq_one.mpr ⟨hu3, hun⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  apply Subtype.ext
  apply Units.ext
  rw [hu, hu1]
  simp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {N L Bs Z : Subgroup G}
variable {Q : Type} [Group Q] {f : ↥N →* Q} {ψ : Su K 2 1 6 →* Q}

omit [Finite G] in
theorem ggQTwoDUnitSix_fixed_of_commute (hK : Nat.card K = 4)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {ω : Kˣ} (hω : orderOf ω = 3) {k : Fin 6}
    {s : ↥N} (hs : qTwoChartTwoThree_induces ψ (f s) (qtwoDB39_delDiag ω k)) {l : ↥N}
    (hls : l * s = s * l) {w : Su K 2 1 6} (hw : ψ w = f l) :
    w ∈ CFSG.ClassicalInvolution.Balance.fixedGroup
      (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω k)) := by
  obtain ⟨w', hw'mat, hψw'⟩ := hs w
  have hψeq : ψ w' = ψ w := by
    rw [hψw', hw, ← map_mul, ← map_inv, ← map_mul, ← hls, mul_inv_cancel_right]
  have hz : w' * w⁻¹ ∈ Subgroup.center (Su K 2 1 6) :=
    hψk (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, mul_inv_cancel])
  have hconj : qtwoDB39_conjAut hK (qtwoDB39_delDiag ω k) w = (w' * w⁻¹) * w := by
    rw [inv_mul_cancel_right]
    exact Subtype.ext (by rw [qtwoDB39_conjAut_apply, hw'mat])
  exact qtwoDB39_fixed_of_conj_scalar hK (by norm_num) hω hz hconj

theorem ggQTwoDUnitSix_conj_mem_coordBlockSU_erase (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {k : Fin 6} {w : Su K 2 1 6}
    (hw : w ∈ CFSG.ClassicalInvolution.Balance.fixedGroup
      (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω k)))
    {v : Su K 2 1 6} (hv : v ∈ coordBlockSU K 2 1 (Finset.univ.erase k)) :
    w * v * w⁻¹ ∈ coordBlockSU K 2 1 (Finset.univ.erase k) := by
  have hω1 : ω ≠ 1 := by
    rintro rfl
    simp at hω
  have hvF : v ∈ CFSG.ClassicalInvolution.Balance.fixedGroup
      (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω k)) :=
    qtwoDB39_coordBlock_le_fixed hK (fun i hi j hj => by
      simp [qtwoDB39_delDiag, (Finset.mem_erase.mp hi).1, (Finset.mem_erase.mp hj).1]) hv
  exact Subgroup.mem_subgroupOf.mp ((qtwoDB39_coordBlock_normal (c := k) hK hω1).conj_mem
    ⟨v, hvF⟩ (Subgroup.mem_subgroupOf.mpr hv) ⟨w, hw⟩)

theorem ggQTwoDUnitSix_P_comp_L (hK : Nat.card K = 4) (hD : NsQuot.Datum p N f L Bs Z)
    (hψr : ψ.range = NsQuot.img N f L) (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    {a c : Fin 6} (hac : a ≠ c) {P : Subgroup G} (hPL : P ≤ L) [Group.IsPerfect ↥P]
    (hPZ : ∀ j ∈ P, j ∈ Z → j = 1)
    (hP : NsQuot.img N f P = (coordBlockSU K 2 1 ((Finset.univ.erase c).erase a)).map ψ)
    {θ : Su K 2 1 ((Finset.univ.erase c).erase a).card →* G} (hθ : Function.Injective θ)
    (hθr : θ.range = P)
    (hθf : ∀ X, ∃ hN : θ X ∈ N,
      f ⟨θ X, hN⟩ = ψ (blockSUOn K 2 1 ((Finset.univ.erase c).erase a) X))
    {b' e' : ↥N} (hb'L : ∀ l ∈ L, (b' : G) * l * (b' : G)⁻¹ ∈ L)
    (he'L : ∀ l ∈ L, (e' : G) * l * (e' : G)⁻¹ ∈ L) {ω : Kˣ} (hω : orderOf ω = 3)
    (hb' : qTwoChartTwoThree_induces ψ (f b') (qtwoDB39_delDiag ω c))
    (he' : qTwoChartTwoThree_induces ψ (f e') (qtwoDB39_delDiag ω a)) :
    IsComponentOf P (L ⊓ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({(e' : G)} : Set G))) := by
  have hcb := ggQTwoDUnitSix_chart_commute hK hD _ hPL hPZ hP hθr hθf hb'L hb'
    (fun i hi => by simp [qtwoDB39_delDiag, (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1])
  have hce := ggQTwoDUnitSix_chart_commute hK hD _ hPL hPZ hP hθr hθf he'L he'
    (fun i hi => by simp [qtwoDB39_delDiag, (Finset.mem_erase.mp hi).1])
  have hPA : P ≤ L ⊓ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({(e' : G)} : Set G)) := fun j hj =>
    Subgroup.mem_inf.mpr ⟨hPL hj, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcb j hj).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr (hce j hj).symm⟩⟩
  have hnorm : ∀ l ∈ L ⊓ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({(e' : G)} : Set G)), ∀ j ∈ P, l * j * l⁻¹ ∈ P := by
    intro l hl
    obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
    obtain ⟨hlb, hle⟩ := Subgroup.mem_inf.mp hlC
    have hlN : l ∈ N := hD.LN hlL
    obtain ⟨w, hw⟩ : f ⟨l, hlN⟩ ∈ ψ.range := by
      rw [hψr]
      exact NsQuot.mem_img.2 ⟨⟨l, hlN⟩, hlL, rfl⟩
    have hwc := ggQTwoDUnitSix_fixed_of_commute hK hψk hω hb' (l := ⟨l, hlN⟩)
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hlb)) hw
    have hwa := ggQTwoDUnitSix_fixed_of_commute hK hψk hω he' (l := ⟨l, hlN⟩)
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hle)) hw
    have hblock : ∀ v ∈ coordBlockSU K 2 1 ((Finset.univ.erase c).erase a),
        w * v * w⁻¹ ∈ coordBlockSU K 2 1 ((Finset.univ.erase c).erase a) := by
      intro v hv
      rw [← ggQTwoDUnitSix_coordBlockSU_erase_inf] at hv ⊢
      obtain ⟨hvc, hva⟩ := Subgroup.mem_inf.mp hv
      exact Subgroup.mem_inf.mpr ⟨ggQTwoDUnitSix_conj_mem_coordBlockSU_erase hK hω hwc hvc,
        ggQTwoDUnitSix_conj_mem_coordBlockSU_erase hK hω hwa hva⟩
    refine hD.conj_mem_of_img hPL ⟨l, hlN⟩ (fun l' hl' => L.mul_mem (L.mul_mem hlL hl')
      (L.inv_mem hlL)) fun q hq => ?_
    rw [hP] at hq ⊢
    obtain ⟨v, hv, rfl⟩ := hq
    rw [← hw, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hblock v hv, rfl⟩
  have hNor : (P.subgroupOf (L ⊓ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({(e' : G)} : Set G)))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm g g.2 n hn⟩
  have hcard : 4 ≤ ((Finset.univ.erase c).erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩),
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  exact ⟨hPA, CFSG.Assembly.IsSubnormal.step hPA hNor (CFSG.Assembly.IsSubnormal.refl _),
    ggQTwoDUnitSix_J_quasisimple hK _ hcard hθ hθr⟩

theorem ggQTwoDUnitSix_commutator_mem (hD : NsQuot.Datum 3 N f L Bs Z) {T : Finset (Fin 6)}
    {P : Subgroup G} (hPL : P ≤ L) (hPZ : ∀ j ∈ P, j ∈ Z → j = 1)
    (hP : NsQuot.img N f P = (coordBlockSU K 2 1 T).map ψ) {i j : Fin 6} (hi : i ∈ T)
    (hj : j ∈ T) (hij : i ≠ j)
    (hperm : ∀ q ∈ NsQuot.img N f Bs, ψ (ggPermSU (Equiv.swap i j)) * q *
      (ψ (ggPermSU (Equiv.swap i j)))⁻¹ ∈ NsQuot.img N f Bs)
    (s : ↥Bs) (hsP : ∀ y ∈ P, (s : G) * y * (s : G)⁻¹ ∈ P) :
    ∃ n : ↥N, f n = ψ (ggPermSU (Equiv.swap i j)) ∧
      (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
      (s : G) * (n : G) * (s : G)⁻¹ * (n : G)⁻¹ ∈ P := by
  have hpermT : ggPermSU (K := K) (f := 1) (Equiv.swap i j) ∈ coordBlockSU K 2 1 T :=
    ggQTwoDUnitSix_coordBlockSU_mono (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj) (qtwoDB12_permSU_mem_coordBlockSU hij)
  obtain ⟨n₀, hn₀P, hn₀⟩ := NsQuot.mem_img.1
    (show ψ (ggPermSU (Equiv.swap i j)) ∈ NsQuot.img N f P by rw [hP]; exact ⟨_, hpermT, rfl⟩)
  have hconj : ∀ b : ↥N, (b : G) ∈ Bs → ∃ b' : ↥N, (b' : G) ∈ Bs ∧ f b' = f (n₀ * b * n₀⁻¹) := by
    intro b hb
    have h := hperm (f b) (NsQuot.mem_img.2 ⟨b, hb, rfl⟩)
    obtain ⟨b', hb', hfb'⟩ := NsQuot.mem_img.1 h
    exact ⟨b', hb', by rw [hfb', map_mul, map_mul, map_inv, hn₀]⟩
  obtain ⟨z, hz, hzn⟩ := hD.exists_normalizer_correction n₀ hconj
  have hzZ : ((z : ↥N) : G) ∈ Z := (hD.mem_ker_iff z).1 hz
  refine ⟨z⁻¹ * n₀, ?_, hzn, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hz, inv_one, one_mul, hn₀]
  set zz : G := ((z : ↥N) : G) with hzz
  set nn : G := ((n₀ : ↥N) : G) with hnn
  have hz₁ : (s : G) * zz⁻¹ * (s : G)⁻¹ ∈ Z := hD.conj_mem (hD.BsN s.2) (Z.inv_mem hzZ)
  have hp : (s : G) * nn * (s : G)⁻¹ * nn⁻¹ ∈ P := P.mul_mem (hsP _ hn₀P) (P.inv_mem hn₀P)
  have hcomm : (s : G) * nn * (s : G)⁻¹ * nn⁻¹ * zz = zz * ((s : G) * nn * (s : G)⁻¹ * nn⁻¹) :=
    (hD.Zcent zz hzZ _ (hPL hp))
  have heq : (s : G) * ((z⁻¹ * n₀ : ↥N) : G) * (s : G)⁻¹ * ((z⁻¹ * n₀ : ↥N) : G)⁻¹ =
      ((s : G) * zz⁻¹ * (s : G)⁻¹ * zz) * ((s : G) * nn * (s : G)⁻¹ * nn⁻¹) := by
    have h1 : ((z⁻¹ * n₀ : ↥N) : G) = zz⁻¹ * nn := rfl
    rw [h1]
    calc (s : G) * (zz⁻¹ * nn) * (s : G)⁻¹ * (zz⁻¹ * nn)⁻¹
        = ((s : G) * zz⁻¹ * (s : G)⁻¹) * (((s : G) * nn * (s : G)⁻¹ * nn⁻¹) * zz) := by group
      _ = ((s : G) * zz⁻¹ * (s : G)⁻¹) * (zz * ((s : G) * nn * (s : G)⁻¹ * nn⁻¹)) := by
          rw [hcomm]
      _ = ((s : G) * zz⁻¹ * (s : G)⁻¹ * zz) * ((s : G) * nn * (s : G)⁻¹ * nn⁻¹) := by group
  rw [heq]
  set z' : G := (s : G) * zz⁻¹ * (s : G)⁻¹ * zz with hz'
  set pp : G := (s : G) * nn * (s : G)⁻¹ * nn⁻¹ with hpp
  have hz'Z : z' ∈ Z := Z.mul_mem hz₁ hzZ
  have hz'p : z' * pp = pp * z' := (hD.Zcent z' hz'Z pp (hPL hp)).symm
  have hBs : z' * pp ∈ Bs := by
    rw [← heq]
    have hnB : ((z⁻¹ * n₀ : ↥N) : G) ∈ Subgroup.normalizer (Bs : Set G) := hzn
    have h2 : ((z⁻¹ * n₀ : ↥N) : G) * (s : G)⁻¹ * ((z⁻¹ * n₀ : ↥N) : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hnB _).mp (Bs.inv_mem s.2)
    have h3 : (s : G) * ((z⁻¹ * n₀ : ↥N) : G) * (s : G)⁻¹ * ((z⁻¹ * n₀ : ↥N) : G)⁻¹ =
        (s : G) * (((z⁻¹ * n₀ : ↥N) : G) * (s : G)⁻¹ * ((z⁻¹ * n₀ : ↥N) : G)⁻¹) := by group
    rw [h3]
    exact Bs.mul_mem s.2 h2
  have h3 : (z' * pp) ^ 3 = 1 := hD.Bsp _ hBs
  have hpow : (z' * pp) ^ 3 = z' ^ 3 * pp ^ 3 := Commute.mul_pow hz'p 3
  have hz'3P : z' ^ 3 ∈ P := by
    have h4 : z' ^ 3 = (pp ^ 3)⁻¹ := by
      rw [hpow] at h3
      exact eq_inv_of_mul_eq_one_left h3
    rw [h4]
    exact P.inv_mem (P.pow_mem hp 3)
  have hz'3 : z' ^ 3 = 1 := hPZ _ hz'3P (Z.pow_mem hz'Z 3)
  obtain ⟨k, hk⟩ := hD.Z2 z' hz'Z
  have hz'1 : z' = 1 := by
    have h1 : orderOf z' ∣ 3 := orderOf_dvd_of_pow_eq_one hz'3
    have h2 : orderOf z' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
  rw [hz'1, one_mul]
  exact hp

omit [Finite G] in
theorem ggQTwoDUnitSix_eq_one_of_central_chart (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n)
    (hn3 : ¬ 3 ∣ n) {P : Subgroup G} {θ : Su K 2 1 n →* G} (hθ : Function.Injective θ)
    (hθr : θ.range = P) : ∀ z ∈ P, (∀ y ∈ P, z * y = y * z) → z = 1 := by
  intro z hz hzc
  rw [← hθr] at hz
  obtain ⟨X, rfl⟩ := hz
  have hX : X ∈ Subgroup.center (Su K 2 1 n) := by
    rw [Subgroup.mem_center_iff]
    intro Y
    apply hθ
    rw [map_mul, map_mul]
    exact (hzc (θ Y) (hθr ▸ ⟨Y, rfl⟩)).symm
  rw [ggQTwoDUnitSix_eq_one_of_mem_center_su hK hn hn3 hX, map_one]

omit [Finite G] in
theorem ggQTwoDUnitSix_comp_eq [Finite G] {H P P' : Subgroup G} (hP : IsComponentOf P H)
    (hP' : IsComponentOf P' H) (hcard : Nat.card ↥P' ≤ Nat.card ↥P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, z * y = y * z) → z = 1) {t : G} (htP : t ∈ P) (htP' : t ∈ P')
    (ht : t ≠ 1) : P = P' := by
  rcases isComponentOf_le_or_commutator_eq_bot hP hP'.2.1 with hle | hcomm
  · exact Subgroup.eq_of_le_of_card_ge hle hcard
  · exfalso
    apply ht
    refine hZ t htP fun y hy => ?_
    have hyC := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hy
    exact (Subgroup.mem_centralizer_iff.mp hyC t htP')

end CFSG.StandardType.QTwo

end
