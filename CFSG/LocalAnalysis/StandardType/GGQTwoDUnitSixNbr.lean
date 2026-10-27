module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixCommon
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitComp
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6
import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitLayer
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggQTwoDUnitSix_three_dvd_card (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n)
    {J : Subgroup G} {θ : Su K 2 1 n →* G} (hθ : Function.Injective θ) (hθr : θ.range = J) :
    3 ∣ Nat.card ↥J := by
  have hcard : Nat.card ↥J = Nat.card (Su K 2 1 n) := by
    rw [← hθr, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hθ, Subgroup.card_top]
  rw [hcard]
  have hT : (Finset.univ.map (Fin.castLEEmb hn) : Finset (Fin n)).card = 3 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h216 := qTwoS34_card_coordBlockSU_three hK hT
  have hdvd := Subgroup.card_dvd_of_le
    (le_top : coordBlockSU K 2 1 (Finset.univ.map (Fin.castLEEmb hn)) ≤ ⊤)
  rw [Subgroup.card_top, h216] at hdvd
  exact dvd_trans (by norm_num) hdvd

omit [Finite G] in
theorem ggQTwoDUnitSix_centralizer_mul (x b e : G) :
    Subgroup.centralizer ({x * e * b} : Set G) ⊓ (Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) =
    Subgroup.centralizer ({x} : Set G) ⊓ (Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h, hb, he⟩
    refine ⟨?_, hb, he⟩
    calc y * x = y * (x * e * b) * b⁻¹ * e⁻¹ := by group
      _ = (x * e * b) * y * b⁻¹ * e⁻¹ := by rw [h]
      _ = x * e * (b * y) * b⁻¹ * e⁻¹ := by group
      _ = x * e * (y * b) * b⁻¹ * e⁻¹ := by rw [hb]
      _ = x * (e * y) * e⁻¹ := by group
      _ = x * (y * e) * e⁻¹ := by rw [he]
      _ = x * y := by group
  · rintro ⟨h, hb, he⟩
    refine ⟨?_, hb, he⟩
    calc y * (x * e * b) = (y * x) * e * b := by group
      _ = x * (y * e) * b := by rw [h]; group
      _ = x * (e * y) * b := by rw [he]
      _ = x * e * (y * b) := by group
      _ = x * e * (b * y) := by rw [hb]
      _ = x * e * b * y := by group

theorem ggQTwoDUnitSix_dSign_eq_self {a c : Fin 6} {v : DVec 6} (ha : v a = 0) (hc : v c = 0) :
    dSign 6 a c v = v := by
  funext k
  rw [dSign_apply_vec]
  split_ifs with h
  · rcases h with rfl | rfl
    · rw [ha, neg_zero]
    · rw [hc, neg_zero]
  · rfl

theorem ggQTwoDUnitSix_dSign_eq_neg {a c : Fin 6} {v : DVec 6}
    (h : ∀ k, k ≠ a → k ≠ c → v k = 0) : dSign 6 a c v = -v := by
  funext k
  rw [dSign_apply_vec, Pi.neg_apply]
  split_ifs with hk
  · rfl
  · rw [h k (fun h' => hk (Or.inl h')) (fun h' => hk (Or.inr h'))]
    exact neg_zero.symm

theorem ggQTwoDUnitSix_dSign_one {a c : Fin 6} (hac : a ≠ c) :
    dSign 6 a c (fun _ => 1) = (fun _ => (1 : ZMod 3)) + Pi.single a 1 + Pi.single c 1 := by
  funext k
  rw [dSign_apply_vec, Pi.add_apply, Pi.add_apply]
  by_cases hka : k = a
  · subst hka
    rw [if_pos (Or.inl rfl), Pi.single_eq_same, Pi.single_eq_of_ne hac]
    show (-1 : ZMod 3) = 1 + 1 + 0
    decide
  · by_cases hkc : k = c
    · subst hkc
      rw [if_pos (Or.inr rfl), Pi.single_eq_of_ne hka, Pi.single_eq_same]
      show (-1 : ZMod 3) = 1 + 0 + 1
      decide
    · rw [if_neg (not_or.mpr ⟨hka, hkc⟩), Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkc,
        add_zero, add_zero]

omit [Finite K] [CharP K 2] in
theorem ggQTwoDUnitSix_single_delDiag (ω : Kˣ) (k : Fin 6) :
    (fun i => ω ^ ((Pi.single k (1 : ZMod 3) : DVec 6) i).val) = qtwoDB39_delDiag ω k := by
  funext i
  simp only [qtwoDB39_delDiag]
  by_cases hik : i = k
  · rw [if_pos hik, hik, Pi.single_eq_same, show (1 : ZMod 3).val = 1 by decide, pow_one]
  · rw [if_neg hik, Pi.single_eq_of_ne hik, ZMod.val_zero, pow_zero]

theorem ggQTwoDUnitSix_Bs_le_normalizer (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {T : Finset (Fin 6)} (hT : T.card < 6) {J : Subgroup G} (hJL : J ≤ L) [Group.IsPerfect ↥J]
    (hJZ : ∀ j ∈ J, j ∈ twoCentral L → j = 1)
    (hJ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J = (coordBlockSU K 2 1 T).map ψ) :
    Bs ≤ Subgroup.normalizer (J : Set G) := by
  have hNL : ∀ n : ↥(Subgroup.normalizer (L : Set G)), ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L :=
    fun n l hl => (Subgroup.mem_normalizer_iff.mp n.2 l).mp hl
  obtain ⟨θ, -, hθr, hθf⟩ := ggQTwoDUnitSix_chart hK hD hψk T hT hJL hJZ hJ
  have hconj : ∀ s : ↥Bs, ∀ j ∈ J, (s : G) * j * (s : G)⁻¹ ∈ J := by
    intro s j hj
    rw [← hθr] at hj ⊢
    obtain ⟨X, rfl⟩ := hj
    exact MonoidHom.mem_range.mpr ⟨_, (ggQTwoDUnitSix_chart_conj hK hD T hJL hJZ hJ hθr hθf
      (s := ⟨s, hD.BsN s.2⟩) (hNL _) (hind s (hD.BsN s.2)) X).symm⟩
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj ⟨s, hs⟩ h, fun hh => ?_⟩
  have h2 := hconj ⟨s, hs⟩⁻¹ (s * h * s⁻¹) hh
  have he : ((⟨s, hs⟩⁻¹ : ↥Bs) : G) * (s * h * s⁻¹) * ((⟨s, hs⟩⁻¹ : ↥Bs) : G)⁻¹ = h := by
    show s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h
    group
  rwa [he] at h2

theorem ggQTwoDUnitSix_sub_single_mem (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {T : Finset (Fin 6)} (hT : T.card < 6) {P : Subgroup G} (hPL : P ≤ L) [Group.IsPerfect ↥P]
    (hPZ : ∀ j ∈ P, j ∈ twoCentral L → j = 1)
    (hP : NsQuot.img (Subgroup.normalizer (L : Set G)) f P = (coordBlockSU K 2 1 T).map ψ)
    {i j : Fin 6} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) :
    ∃ t : ↥Bs, (t : G) ∈ P ∧ βL (Additive.ofMul t) = Pi.single i 1 + -Pi.single j 1 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ↥Bs, βL (Additive.ofMul s) = Pi.single i 1 :=
    ⟨Additive.toMul (βL.symm (Pi.single i 1)), by simp⟩
  have hsP : ∀ y ∈ P, (s : G) * y * (s : G)⁻¹ ∈ P := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (ggQTwoDUnitSix_Bs_le_normalizer hK hD hψk hind hT hPL hPZ hP s.2) y).mp hy
  have hperm : ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU (Equiv.swap i j)) * q * (ψ (ggPermSU (Equiv.swap i j)))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs := by
    intro q hq
    have h := hε (Equiv.swap i j) q hq
    rwa [Equiv.swap_inv] at h
  obtain ⟨n, hnf, hnB, htP⟩ := ggQTwoDUnitSix_commutator_mem hD hPL hPZ hP hi hj hij hperm s hsP
  obtain ⟨y, hy⟩ : ∃ y : ↥Bs, (y : G) = (n : G) * s * (n : G)⁻¹ :=
    ⟨⟨_, (Subgroup.mem_normalizer_iff.mp hnB _).mp s.2⟩, rfl⟩
  have hβy : βL (Additive.ofMul y) = Pi.single j 1 := by
    have hfy : f ⟨(y : G), hD.BsN y.2⟩ = ψ (ggPermSU (Equiv.swap i j)⁻¹) *
        f ⟨(s : G), hD.BsN s.2⟩ * (ψ (ggPermSU (Equiv.swap i j)⁻¹))⁻¹ := by
      rw [Equiv.swap_inv, ← hnf, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext hy)
    have hdb : ∀ k : Fin 6, dBasis 6 k = (Pi.single k 1 : DVec 6) := fun k => by simp [dBasis]
    rw [hpermβ (Equiv.swap i j) s y (hD.BsN s.2) (hD.BsN y.2) hfy, hs, ← hdb i, dPerm_apply,
      Equiv.swap_apply_left, hdb]
  refine ⟨s * y⁻¹, ?_, ?_⟩
  · have htG : ((s * y⁻¹ : ↥Bs) : G) = (s : G) * n * (s : G)⁻¹ * (n : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy]
      group
    rw [htG]
    exact htP
  · rw [ofMul_mul, ofMul_inv, map_add, map_neg, hs, hβy]

open scoped commutatorElement in
theorem ggQTwoDUnitSix_common (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {x : G} (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxBs : x ∈ Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L)
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    ∃ P : Subgroup G, P ≤ J₁ ∧ P ≤ J₁.map (MulAut.conj g).toMonoidHom ∧ ⁅P, P⁆ = P ∧
      3 ∣ Nat.card ↥P := by
  classical
  have hNL : ∀ n : ↥(Subgroup.normalizer (L : Set G)), ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L :=
    fun n l hl => (Subgroup.mem_normalizer_iff.mp n.2 l).mp hl
  have hsingle : ∀ k : Fin 6, ∃ s : ↥Bs, βL (Additive.ofMul s) = Pi.single k 1 :=
    fun k => ⟨Additive.toMul (βL.symm (Pi.single k 1)), by simp⟩
  have hdiag : ∀ (s : ↥Bs) (k : Fin 6), βL (Additive.ofMul s) = Pi.single k 1 →
      qTwoChartTwoThree_induces ψ (f ⟨s, hD.BsN s.2⟩) (qtwoDB39_delDiag ω k) := by
    intro s k hs
    have hfun : (fun i => ω ^ (βL (Additive.ofMul s) i).val) = qtwoDB39_delDiag ω k := by
      rw [hs]
      exact ggQTwoDUnitSix_single_delDiag ω k
    rw [← hfun]
    exact hind s (hD.BsN s.2)
  have hβmul : ∀ s t : ↥Bs, βL (Additive.ofMul (s * t)) =
      βL (Additive.ofMul s) + βL (Additive.ofMul t) := fun s t => by
    rw [ofMul_mul, map_add]
  have hβinv : ∀ s : ↥Bs, βL (Additive.ofMul s⁻¹) = -βL (Additive.ofMul s) := fun s => by
    rw [ofMul_inv, map_neg]
  have hβinj : ∀ s t : ↥Bs, βL (Additive.ofMul s) = βL (Additive.ofMul t) → s = t :=
    fun s t h => Additive.ofMul.injective (βL.injective h)
  obtain ⟨b', hb'⟩ := hsingle c
  obtain ⟨e', he'⟩ := hsingle a
  have hgb : g * (b' : G) * g⁻¹ = (b' : G)⁻¹ := by
    have h : α b' = b'⁻¹ := hβinj _ _ (by
      rw [hα, hβinv, hb']
      exact ggQTwoDUnitSix_dSign_eq_neg fun k _ hkc => by rw [Pi.single_eq_of_ne hkc])
    exact (hg b').symm.trans (congrArg Subtype.val h)
  have hge : g * (e' : G) * g⁻¹ = (e' : G)⁻¹ := by
    have h : α e' = e'⁻¹ := hβinj _ _ (by
      rw [hα, hβinv, he']
      exact ggQTwoDUnitSix_dSign_eq_neg fun k hka _ => by rw [Pi.single_eq_of_ne hka])
    exact (hg e').symm.trans (congrArg Subtype.val h)
  have hgx : g * x * g⁻¹ = x * (e' : G) * (b' : G) := by
    have h : α ⟨x, hxBs⟩ = ⟨x, hxBs⟩ * e' * b' := hβinj _ _ (by
      rw [hα, hβmul, hβmul, hxcoord, hb', he']
      exact ggQTwoDUnitSix_dSign_one hac)
    exact (hg ⟨x, hxBs⟩).symm.trans (congrArg Subtype.val h)
  have hRcard : ((Finset.univ.erase c).erase a).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩),
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = J₁ ⊓
      (((coordBlockSU K 2 1 ((Finset.univ.erase c).erase a)).map ψ).comap f).map
        (Subgroup.normalizer (L : Set G)).subtype := ⟨_, rfl⟩
  have hPJ : P ≤ J₁ := by
    rw [hPdef]
    exact inf_le_left
  have hPL : P ≤ L := hPJ.trans hJ₁L
  have hPZ : ∀ j ∈ P, j ∈ twoCentral L → j = 1 := fun j hj => hJ₁Z j (hPJ hj)
  have hPimg : NsQuot.img (Subgroup.normalizer (L : Set G)) f P =
      (coordBlockSU K 2 1 ((Finset.univ.erase c).erase a)).map ψ := by
    apply le_antisymm
    · intro q hq
      obtain ⟨u, huP, rfl⟩ := NsQuot.mem_img.mp hq
      rw [hPdef] at huP
      obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp huP).2
      rw [show u = n from Subtype.ext hnu.symm]
      exact hn
    · intro q hq
      have hq1 : q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ := by
        rw [hJ₁]
        exact Subgroup.map_mono (ggQTwoDUnitSix_coordBlockSU_mono (Finset.erase_subset _ _)) hq
      obtain ⟨u, huJ, rfl⟩ := NsQuot.mem_img.mp hq1
      refine NsQuot.mem_img.mpr ⟨u, ?_, rfl⟩
      rw [hPdef]
      exact Subgroup.mem_inf.mpr ⟨huJ, Subgroup.mem_map.mpr ⟨u, hq, rfl⟩⟩
  obtain ⟨θ, hθ, hθr, hθf⟩ := ggQTwoDUnitSix_chart hK hD hψk ((Finset.univ.erase c).erase a)
    (by omega) hPL hPZ hPimg
  have hPperf : Group.IsPerfect ↥P := by
    have : Group.IsPerfect (Su K 2 1 ((Finset.univ.erase c).erase a).card) :=
      isPerfect_Su hK hRcard.ge
    rw [← hθr]
    exact Group.IsPerfect.range θ
  have hPc := ggQTwoDUnitSix_P_comp_L hK hD hψr hψk hac hPL hPZ hPimg hθ hθr hθf
    (b' := ⟨b', hD.BsN b'.2⟩) (e' := ⟨e', hD.BsN e'.2⟩) (hNL _) (hNL _) hω (hdiag b' c hb')
    (hdiag e' a he')
  have hPx : IsComponentOf P (Subgroup.centralizer ({x} : Set G) ⊓
      (Subgroup.centralizer ({(b' : G)} : Set G) ⊓ Subgroup.centralizer ({(e' : G)} : Set G))) :=
    isComponentOf_of_isSubnormal_of_isComponentOf hPc
      (LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1 _)
  have hmapH : (Subgroup.centralizer ({x} : Set G) ⊓
      (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
        Subgroup.centralizer ({(e' : G)} : Set G))).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({x} : Set G) ⊓ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
        Subgroup.centralizer ({(e' : G)} : Set G)) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ggQTwoDUnitSix_map_centralizer_conj,
      ggQTwoDUnitSix_map_centralizer_conj, ggQTwoDUnitSix_map_centralizer_conj, hgx, hgb, hge,
      ggQTwoDUnitSix_centralizer_inv, ggQTwoDUnitSix_centralizer_inv,
      ggQTwoDUnitSix_centralizer_mul]
  have hP₂ : IsComponentOf (P.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({x} : Set G) ⊓ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
        Subgroup.centralizer ({(e' : G)} : Set G))) := by
    rw [← hmapH]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mpr hPx
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (show 1 < ((Finset.univ.erase c).erase a).card by omega)
  have hia : i ≠ a := (Finset.mem_erase.mp hi).1
  have hic : i ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hja : j ≠ a := (Finset.mem_erase.mp hj).1
  have hjc : j ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  obtain ⟨t, htP', hβt⟩ := ggQTwoDUnitSix_sub_single_mem hK hD hψk hε hind hpermβ
    (by omega : ((Finset.univ.erase c).erase a).card < 6) hPL hPZ hPimg hi hj hij
  have hαt : α t = t := hβinj _ _ (by
    rw [hα, hβt]
    refine ggQTwoDUnitSix_dSign_eq_self ?_ ?_
    · rw [Pi.add_apply, Pi.neg_apply, Pi.single_eq_of_ne hia.symm, Pi.single_eq_of_ne hja.symm]
      decide
    · rw [Pi.add_apply, Pi.neg_apply, Pi.single_eq_of_ne hic.symm, Pi.single_eq_of_ne hjc.symm]
      decide)
  have hgt : g * (t : G) * g⁻¹ = (t : G) := by
    rw [← hg, hαt]
  have htP₂ : (t : G) ∈ P.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, htP', hgt⟩
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    have h0 : βL (Additive.ofMul t) = 0 := by
      rw [show t = 1 from Subtype.ext h1, ofMul_one, map_zero]
    have h2 := congrFun (hβt.symm.trans h0) i
    rw [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.zero_apply] at h2
    exact absurd h2 (by decide)
  have hZ := ggQTwoDUnitSix_eq_one_of_central_chart hK (by omega) (by omega) hθ hθr
  have hPP : P = P.map (MulAut.conj g).toMonoidHom :=
    ggQTwoDUnitSix_comp_eq hPx hP₂
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective)) hZ htP' htP₂ ht1
  refine ⟨P, hPJ, ?_, Subgroup.commutator_eq_self,
    ggQTwoDUnitSix_three_dvd_card hK (by omega) hθ hθr⟩
  rw [hPP]
  exact Subgroup.map_mono hPJ

theorem ggQTwoDUnitSix_exists_N
    (hBal : GGLBalanceInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    (hBs : Nat.card ↥Bs = 3 ^ 6) (hK : Nat.card K = 4) {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    (hxBs : x ∈ Bs) {βL : Additive ↥Bs ≃+ DVec 6}
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {ω : Kˣ} (hω : orderOf ω = 3)
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
    {g : G} (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) :
    ∃ N : Subgroup G, LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N ∧
      J₁ ≤ N ∧ J₁.map (MulAut.conj g).toMonoidHom ≤ N := by
  classical
  have hThmI : GGThmIHyp 3 B x L := hcfg.1.1.1.1
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    (hcfg.1.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar 3 B x L).2.2.2.1
  have hBsE : CFSG.Open.IsElemAbelian 3 Bs := (hcfg.1.1.1.2.1 : GGBstar 3 B Bs).2.1
  have hNL : ∀ n : ↥(Subgroup.normalizer (L : Set G)), ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L :=
    fun n l hl => (Subgroup.mem_normalizer_iff.mp n.2 l).mp hl
  have hb'd : qTwoChartTwoThree_induces ψ (f ⟨b', hD.BsN b'.2⟩) (qtwoDB39_delDiag ω c) := by
    have hfun : (fun i => ω ^ (βL (Additive.ofMul b') i).val) = qtwoDB39_delDiag ω c := by
      rw [hb']
      exact ggQTwoDUnitSix_single_delDiag ω c
    rw [← hfun]
    exact hind b' (hD.BsN b'.2)
  have hgb : g * (b' : G) * g⁻¹ = (b' : G)⁻¹ := by
    have h : α b' = b'⁻¹ := by
      apply Additive.ofMul.injective
      apply βL.injective
      rw [hα, ofMul_inv, map_neg, hb']
      exact ggQTwoDUnitSix_dSign_eq_neg fun k _ hkc => by rw [Pi.single_eq_of_ne hkc]
    exact (hg b').symm.trans (congrArg Subtype.val h)
  have hb'1 : (b' : G) ≠ 1 := by
    intro h1
    have h0 : βL (Additive.ofMul b') = 0 := by
      rw [show b' = 1 from Subtype.ext h1, ofMul_one, map_zero]
    have h2 := congrFun (hb'.symm.trans h0) c
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    exact absurd h2 (by decide)
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  obtain ⟨θ, hθ, hθr, hθf⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c) (by omega)
    hJ₁L hJ₁Z hJ₁
  have hc₁ : IsComponentOf J₁ (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) :=
    ggQTwoDUnitSix_J_comp hK hD hψr c hJ₁L hJ₁Z hJ₁ hψk hθ hθr hθf (b' := ⟨b', hD.BsN b'.2⟩)
      (hNL _) hω hb'd hL
  have hc₂ := ggQTwoDUnitSix_conj_comp hgb hc₁
  have hxH : x ∈ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE hxBs b'.2
  have hgxBs : g * x * g⁻¹ ∈ Bs := by
    rw [← hg ⟨x, hxBs⟩]
    exact (α ⟨x, hxBs⟩).2
  have hx'H : g * x * g⁻¹ ∈ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE hgxBs b'.2
  have hx3 : x ^ 3 = 1 := hD.Bsp x hxBs
  have hx'3 : (g * x * g⁻¹) ^ 3 = 1 := hD.Bsp _ hgxBs
  have h3₁ : 3 ∣ Nat.card ↥J₁ := ggQTwoDUnitSix_three_dvd_card hK (by omega) hθ hθr
  have h3₂ : 3 ∣ Nat.card ↥(J₁.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3₁
  have hl₁ := ggQTwoDUnitSix_layer hBal hThmI hb'1 hxH hx3 hc₁ h3₁
  have hl₂ := ggQTwoDUnitSix_layer hBal hThmI hb'1 hx'H hx'3 hc₂ h3₂
  obtain ⟨P, hP₁, hP₂, hPperf, hP3⟩ := ggQTwoDUnitSix_common hK hD hψr hψk hε hL hxBs hxcoord
    hω hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hg
  have hJ₁' : ∃ θ : Su K 2 1 (Finset.univ.erase c).card →* G, Function.Injective θ ∧
      θ.range = J₁ := ⟨θ, hθ, hθr⟩
  rw [h5] at hJ₁'
  obtain ⟨θ₅, hθ₅, hθ₅r⟩ := hJ₁'
  exact ggQTwoDUnit_one_component hK (le_refl 5) ⟨θ₅, hθ₅, hθ₅r⟩
    ⟨(MulAut.conj g).toMonoidHom.comp θ₅, (MulAut.conj g).injective.comp hθ₅, by
      rw [MonoidHom.range_comp, hθ₅r]⟩
    hxH hx'H hx3 hx'3 hc₁ hc₂ hl₁ hl₂ hP₁ hP₂ hPperf hP3
    (fun E hE hU => ggQTwoDUnit_rank_bound_of_card hcfg rfl hBs E hE hU)

end CFSG.StandardType.QTwo

end
