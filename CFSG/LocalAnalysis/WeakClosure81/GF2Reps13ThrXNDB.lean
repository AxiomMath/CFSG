module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNDA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

variable {A Q O : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16n_map_mul (U : Subgroup W) (g h : MulAut W) :
    (U.map g.toMonoidHom).map h.toMonoidHom = U.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16n_map_one (U : Subgroup W) :
    U.map (1 : MulAut W).toMonoidHom = U := by
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16n_map_conj_inv (U : Subgroup (MulAut W)) (g : MulAut W) :
    (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp [MulAut.conj_apply]
  rw [h, Subgroup.map_id]

private theorem w16n_conj_mem_centSub_map_iff (U : Subgroup W) (g : MulAut W) (y : MulAut W) :
    g * y * g⁻¹ ∈ centSub (U.map g.toMonoidHom) ↔ y ∈ centSub U := by
  rw [mem_centSub, mem_centSub]
  constructor
  · intro hh u hu
    have hgu : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have h1 : (g * y * g⁻¹) (g u) = g u := hh (g u) hgu
    have h2 : (g * y * g⁻¹) (g u) = g (y u) := by simp [MulAut.mul_apply]
    rw [h2] at h1
    exact g.injective h1
  · intro hh u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have hv' : y v = v := hh v hv
    simp [MulAut.mul_apply, hv']

private theorem w16n_kerOn_map_eq (h : HNon A Q O t) {x : MulAut W} (hxO : x ∈ O)
    {U : Subgroup W} (hU : U ∈ s13IsoComps Q) :
    s13KerOn Q (U.map x.toMonoidHom) = (s13KerOn Q U).map (MulAut.conj x).toMonoidHom := by
  ext z
  constructor
  · intro hz
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * z * x, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact h.hQN x⁻¹ (O.inv_mem hxO) z hz.1
      · have hzeq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        have hz' : x * (x⁻¹ * z * x) * x⁻¹ ∈ centSub (U.map x.toMonoidHom) := by
          rw [hzeq]; exact hz.2
        exact (w16n_conj_mem_centSub_map_iff U x (x⁻¹ * z * x)).mp hz'
    · change x * (x⁻¹ * z * x) * x⁻¹ = z
      group
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    rw [← hyz]
    exact ⟨h.hQN x hxO y hy.1, (w16n_conj_mem_centSub_map_iff U x y).mpr hy.2⟩

private theorem w16n_kerOn_card (h : HNon A Q O t) {U : Subgroup W}
    (hU : U ∈ s13IsoComps Q) : Nat.card (s13KerOn Q U) = 3 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hle, hrel⟩ := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hQe hU
  have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U) (K := Q)
  rw [inf_eq_left.mpr hle, hrel, (w16n_shape_aux h).1] at hm
  omega

private theorem w16n_Q_odd (h : HNon A Q O t) : Odd (Nat.card ↥Q) := by
  rw [(w16n_shape_aux h).1]
  norm_num

private theorem w16n_perm_fix_of_three (h : HNon A Q O t) {y : MulAut W} (hy3 : y ^ 3 = 1)
    (hperm : ∀ V ∈ s13IsoComps Q, V.map y.toMonoidHom ∈ s13IsoComps Q)
    {U V W' : Subgroup W} (hU : U ∈ s13IsoComps Q) (hV : V ∈ s13IsoComps Q)
    (hW' : W' ∈ s13IsoComps Q) (hUV : U ≠ V) (hUW : U ≠ W') (hVW : V ≠ W')
    (hfixU : U.map y.toMonoidHom = U) : V.map y.toMonoidHom = V := by
  classical
  have hS3 : (s13IsoComps Q).ncard = 3 := (w16n_shape_aux h).2.1
  have hcard : ({U, V, W'} : Set (Subgroup W)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨U, V, W', hUV, hUW, hVW, rfl⟩
  have hsub : ({U, V, W'} : Set (Subgroup W)) ⊆ s13IsoComps Q := by
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with rfl | rfl | rfl <;> assumption
  have heq : ({U, V, W'} : Set (Subgroup W)) = s13IsoComps Q :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hS3])
  have hinj : Function.Injective (fun Z : Subgroup W => Z.map y.toMonoidHom) :=
    fun a b hab => Subgroup.map_injective y.injective hab
  have hmemV : V.map y.toMonoidHom ∈ ({U, V, W'} : Set (Subgroup W)) := by
    rw [heq]; exact hperm V hV
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemV
  rcases hmemV with h | h | h
  · exfalso
    have : V = U := hinj (by simp only [h, hfixU])
    exact hUV this.symm
  · exact h
  · exfalso
    have hmemW : W'.map y.toMonoidHom ∈ ({U, V, W'} : Set (Subgroup W)) := by
      rw [heq]; exact hperm W' hW'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemW
    rcases hmemW with h2 | h2 | h2
    · have : W' = U := hinj (by simp only [h2, hfixU])
      exact hUW this.symm
    ·
      have h2' : (V.map y.toMonoidHom).map y.toMonoidHom = V := by rw [h, h2]
      have h3 : V.map y.toMonoidHom = V := by
        have h4 : ((V.map y.toMonoidHom).map y.toMonoidHom).map y.toMonoidHom =
            V.map y.toMonoidHom := by rw [h2']
        have h5 : ((V.map y.toMonoidHom).map y.toMonoidHom).map y.toMonoidHom = V := by
          rw [w16n_map_mul, w16n_map_mul]
          rw [show y * y * y = 1 from by rw [mul_assoc, ← pow_three]; exact hy3]
          exact w16n_map_one V
        exact h4.symm.trans h5
      exact hVW (h3.symm.trans h)
    ·
      have h4 : ((V.map y.toMonoidHom).map y.toMonoidHom).map y.toMonoidHom = V := by
        rw [w16n_map_mul, w16n_map_mul]
        rw [show y * y * y = 1 from by rw [mul_assoc, ← pow_three]; exact hy3]
        exact w16n_map_one V
      have h5 : ((V.map y.toMonoidHom).map y.toMonoidHom).map y.toMonoidHom = W' := by
        rw [h, h2, h2]
      exact hVW (h4.symm.trans h5)

private theorem w16n_map_fix_all (h : HNon A Q O t) {y : MulAut W} (hy3 : y ^ 3 = 1)
    (hperm : ∀ V ∈ s13IsoComps Q, V.map y.toMonoidHom ∈ s13IsoComps Q)
    {U : Subgroup W} (hU : U ∈ s13IsoComps Q) (hfixU : U.map y.toMonoidHom = U) :
    ∀ V ∈ s13IsoComps Q, V.map y.toMonoidHom = V := by
  classical
  obtain ⟨U₁, U₂, U₃, h12, h13, h23, hSeq⟩ := Set.ncard_eq_three.mp (w16n_shape_aux h).2.1
  have hU1 : U₁ ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hU2 : U₂ ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hU3 : U₃ ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hUmem : U = U₁ ∨ U = U₂ ∨ U = U₃ := by
    have : U ∈ ({U₁, U₂, U₃} : Set (Subgroup W)) := by rw [← hSeq]; exact hU
    simpa using this
  have hall : U₁.map y.toMonoidHom = U₁ ∧ U₂.map y.toMonoidHom = U₂ ∧
      U₃.map y.toMonoidHom = U₃ := by
    rcases hUmem with rfl | rfl | rfl
    · have h2 := w16n_perm_fix_of_three h hy3 hperm hU1 hU2 hU3 h12 h13 h23 hfixU
      have h3 := w16n_perm_fix_of_three h hy3 hperm hU1 hU3 hU2 h13 h12 h23.symm hfixU
      exact ⟨hfixU, h2, h3⟩
    · have h1 := w16n_perm_fix_of_three h hy3 hperm hU2 hU1 hU3 h12.symm h23 h13 hfixU
      have h3 := w16n_perm_fix_of_three h hy3 hperm hU2 hU3 hU1 h23 h12.symm h13.symm hfixU
      exact ⟨h1, hfixU, h3⟩
    · have h1 := w16n_perm_fix_of_three h hy3 hperm hU3 hU1 hU2 h13.symm h23.symm h12 hfixU
      have h2 := w16n_perm_fix_of_three h hy3 hperm hU3 hU2 hU1 h23.symm h13.symm h12.symm hfixU
      exact ⟨h1, h2, hfixU⟩
  intro V hV
  rw [hSeq] at hV
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hV
  rcases hV with rfl | rfl | rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

private theorem w16n_commutator_le_left (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A) :
    ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hbO : b ∈ O := w16n_Qg_le_O h hg hb
  have hb' : b * a⁻¹ * b⁻¹ ∈ Q := h.hQN b hbO a⁻¹ (Q.inv_mem ha)
  rw [commutatorElement_def]
  rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
  exact Q.mul_mem ha hb'

private theorem w16n_commutator_le_right (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A) :
    ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≤ Q.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : a * b * a⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom :=
    (Subgroup.le_normalizer_iff.mp (w16n_O_le_normalizer_Qg h hg)) a (h.hQO ha) b hb
  rw [commutatorElement_def]
  rw [show a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹) * b⁻¹ by rfl]
  exact (Q.map (MulAut.conj g).toMonoidHom).mul_mem hab
    ((Q.map (MulAut.conj g).toMonoidHom).inv_mem hb)

private theorem w16n_exists_zpowers_comm_ne_bot (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ y ∈ Q.map (MulAut.conj g).toMonoidHom, ⁅Q, Subgroup.zpowers y⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply hcomm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hbot : ⁅Q, Subgroup.zpowers y⁆ = ⊥ := hcon y hy
  have hle : Q ≤ Subgroup.centralizer (Subgroup.zpowers y : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  exact (Subgroup.mem_centralizer_iff.mp (hle hq)) y (Subgroup.mem_zpowers y)

private theorem w16n_commutator_card (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    Nat.card ↥(⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ : Subgroup (MulAut W)) = 3 := by
  have hp3 : Nat.Prime 3 := by norm_num
  set Z : Subgroup (MulAut W) := ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ with hZdef
  have hcomm' : Z ≠ ⊥ := by rw [hZdef]; exact hcomm
  have hZQ : Z ≤ Q := by rw [hZdef]; exact w16n_commutator_le_left h hg
  have hZQg : Z ≤ Q.map (MulAut.conj g).toMonoidHom := by
    rw [hZdef]; exact w16n_commutator_le_right h hg
  have hZneQ : Z ≠ Q := by
    intro heq
    have hQleQg : Q ≤ Q.map (MulAut.conj g).toMonoidHom :=
      (le_of_eq heq.symm).trans hZQg
    have hcardQg : Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Q :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hQeq : Q = Q.map (MulAut.conj g).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hQleQg (by rw [hcardQg])
    have hraw : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
      rw [← hQeq, Subgroup.commutator_self_eq_bot_iff.mpr h.hQe.1]
    exact hcomm hraw
  have hdvd : Nat.card Z ∣ 9 := by
    have := Subgroup.card_dvd_of_le hZQ
    rwa [(w16n_shape_aux h).1] at this
  have hne1 : Nat.card Z ≠ 1 := fun h1 => hcomm' (Subgroup.card_eq_one.mp h1)
  have hne9 : Nat.card Z ≠ 9 := fun h9 =>
    hZneQ (Subgroup.eq_of_le_of_card_ge hZQ (by rw [h9, (w16n_shape_aux h).1]))
  have hdvd' : Nat.card Z ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]
    exact hdvd
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp3).1 hdvd'
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · exact (hne1 (by rw [hk_eq]; norm_num)).elim
  · rw [hk_eq]
    norm_num
  · exact (hne9 (by rw [hk_eq]; norm_num)).elim

private theorem w16n_commutator_not_le_ker (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∀ U ∈ s13IsoComps Q, ¬ ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≤ s13KerOn Q U := by
  classical
  let Z : Subgroup (MulAut W) := ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆
  have hZ3 : Nat.card Z = 3 := w16n_commutator_card h hg hcomm
  have hZQg : Z ≤ Q.map (MulAut.conj g).toMonoidHom := w16n_commutator_le_right h hg
  intro U hU hZU
  have hHU : s13KerOn Q U = Z :=
    (Subgroup.eq_of_le_of_card_ge hZU (by rw [hZ3, w16n_kerOn_card h hU])).symm
  obtain ⟨y, hyQg, hyne⟩ := w16n_exists_zpowers_comm_ne_bot h hg hcomm
  have hyO : y ∈ O := (w16n_Qg_le_O h hg) hyQg
  have hyQN : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq => h.hQN y hyO q hq
  have hyQN' : ∀ q ∈ Q, y⁻¹ * q * y ∈ Q := fun q hq => by
    have := h.hQN y⁻¹ (O.inv_mem hyO) q hq
    simpa using this
  have hperm : ∀ V ∈ s13IsoComps Q, V.map y.toMonoidHom ∈ s13IsoComps Q :=
    fun V hV => map_mem_s13IsoComps hyQN hyQN' hV
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨q, hq, hyq⟩ := Subgroup.mem_map.mp hyQg
    rw [← hyq]
    change ((MulAut.conj g) q) ^ 3 = 1
    rw [← map_pow, h.hQe.2 q hq, map_one]
  have hZmap : Z.map (MulAut.conj y).toMonoidHom = Z := by
    show (⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj y).toMonoidHom = _
    rw [Subgroup.map_commutator]
    have hnormQ : ∀ n ∈ O, ∀ x ∈ Q, n * x * n⁻¹ ∈ Q := fun n hn x hx => h.hQN n hn x hx
    have hnormQg : ∀ n ∈ O, ∀ x ∈ Q.map (MulAut.conj g).toMonoidHom, n * x * n⁻¹ ∈
        Q.map (MulAut.conj g).toMonoidHom := fun n hn x hx =>
      (Subgroup.le_normalizer_iff.mp (w16n_O_le_normalizer_Qg h hg)) n hn x hx
    rw [s13_map_conj_eq_of_normalizes hnormQ hyO,
      s13_map_conj_eq_of_normalizes hnormQg hyO]
  have hfixU : U.map y.toMonoidHom = U := by
    have hker : s13KerOn Q (U.map y.toMonoidHom) = s13KerOn Q U := by
      rw [w16n_kerOn_map_eq h hyO hU]
      rw [hHU]
      exact hZmap
    exact (w16n_components_kernel h) (U.map y.toMonoidHom) (hperm U hU) U hU hker
  have hfixAll := w16n_map_fix_all h hy3 hperm hU hfixU
  have hnormHU : y ∈ Subgroup.normalizer (s13KerOn Q U : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hHU]
    exact hZmap
  have hcentHU : Subgroup.zpowers y ≤
      Subgroup.centralizer (s13KerOn Q U : Set (MulAut W)) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq (p := 3) (by norm_num)
      (h.hO3.to_le (Subgroup.zpowers_le.mpr hyO)) (w16n_kerOn_card h hU)
      (Subgroup.zpowers_le.mpr hnormHU)
  obtain ⟨V, hV, hVU⟩ := Set.exists_ne_of_one_lt_ncard (by rw [(w16n_shape_aux h).2.1]; norm_num) U
  have hfixV : V.map y.toMonoidHom = V := hfixAll V hV
  have hnormHV : y ∈ Subgroup.normalizer (s13KerOn Q V : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hker := w16n_kerOn_map_eq h hyO hV
    rw [hfixV] at hker
    exact hker.symm
  have hcentHV : Subgroup.zpowers y ≤
      Subgroup.centralizer (s13KerOn Q V : Set (MulAut W)) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq (p := 3) (by norm_num)
      (h.hO3.to_le (Subgroup.zpowers_le.mpr hyO)) (w16n_kerOn_card h hV)
      (Subgroup.zpowers_le.mpr hnormHV)
  have hQeq : s13KerOn Q U ⊔ s13KerOn Q V = Q := by
    have hp32 : (3 : ℕ) ≠ 2 := by norm_num
    have hle : s13KerOn Q U ⊔ s13KerOn Q V ≤ Q :=
      sup_le (s13KerOn_mem_hyperplanes h.hW (by norm_num) hp32 h.hQe hU).1
        (s13KerOn_mem_hyperplanes h.hW (by norm_num) hp32 h.hQe hV).1
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hne : s13KerOn Q U ≠ s13KerOn Q V := fun heq =>
      hVU ((w16n_components_kernel h) U hU V hV heq).symm
    have hinf : s13KerOn Q U ⊓ s13KerOn Q V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hle_inf : s13KerOn Q U ⊓ s13KerOn Q V ≤ s13KerOn Q U := inf_le_left
      have hdvd : Nat.card ↥(s13KerOn Q U ⊓ s13KerOn Q V) ∣ 3 := by
        have := Subgroup.card_dvd_of_le hle_inf
        rwa [w16n_kerOn_card h hU] at this
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · have hbot : s13KerOn Q U ⊓ s13KerOn Q V = ⊥ := Subgroup.card_eq_one.mp h1
        exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hx))
      · exfalso
        have heqUV : s13KerOn Q U ⊓ s13KerOn Q V = s13KerOn Q U :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, w16n_kerOn_card h hU])
        have hleUV : s13KerOn Q U ≤ s13KerOn Q V := heqUV ▸ inf_le_right
        exact hne (Subgroup.eq_of_le_of_card_ge hleUV
          (by rw [w16n_kerOn_card h hV, w16n_kerOn_card h hU]))
    have hsupdvd : Nat.card ↥(s13KerOn Q U ⊔ s13KerOn Q V) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [(w16n_shape_aux h).1] at this
    have hsupge : 3 ≤ Nat.card ↥(s13KerOn Q U ⊔ s13KerOn Q V) := by
      have hd := Subgroup.card_dvd_of_le
        (le_sup_left : s13KerOn Q U ≤ s13KerOn Q U ⊔ s13KerOn Q V)
      rw [w16n_kerOn_card h hU] at hd
      exact Nat.le_of_dvd Nat.card_pos hd
    have hsupne3 : Nat.card ↥(s13KerOn Q U ⊔ s13KerOn Q V) ≠ 3 := by
      intro h3
      have heq : s13KerOn Q U = s13KerOn Q U ⊔ s13KerOn Q V :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, w16n_kerOn_card h hU])
      have hleVU : s13KerOn Q V ≤ s13KerOn Q U := by rw [heq]; exact le_sup_right
      exact hne (Subgroup.eq_of_le_of_card_ge hleVU
        (by rw [w16n_kerOn_card h hU, w16n_kerOn_card h hV])).symm
    have h9 : Nat.card ↥(s13KerOn Q U ⊔ s13KerOn Q V) = 9 := by
      have hdvd' : Nat.card ↥(s13KerOn Q U ⊔ s13KerOn Q V) ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]
        exact hsupdvd
      obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd'
      have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk_cases with rfl | rfl | rfl
      · rw [hk] at hsupge
        norm_num at hsupge
      · exact absurd (by rw [hk]; norm_num) hsupne3
      · rw [hk]
        norm_num
    rw [h9, (w16n_shape_aux h).1]
  have hcentQ : Q ≤ Subgroup.centralizer (Subgroup.zpowers y : Set (MulAut W)) := by
    rw [← hQeq]
    exact sup_le (Subgroup.le_centralizer_iff.mp hcentHU) (Subgroup.le_centralizer_iff.mp hcentHV)
  exact hyne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentQ)

private theorem w16n_commSub_top_eq_line (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    commSub ⊤ Q = commSub ⊤ ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hZQ : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≤ Q := w16n_commutator_le_left h hg
  have hsupp : s13Supp Q ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ = s13IsoComps Q := by
    ext U
    constructor
    · intro hU; exact hU.1
    · intro hU
      refine ⟨hU, ?_⟩
      have hnot := w16n_commutator_not_le_ker h hg hcomm U hU
      rw [(s13IsoComps_commSub_eq h.hW hp3 hp32 h.hQe hZQ hU).2 hnot]
      exact (s13IsoComps_le_commSub h.hW (w16n_Q_odd h) hU).1
  calc commSub ⊤ Q = ⨆ U ∈ s13IsoComps Q, U := (iSup_s13IsoComps h.hW (w16n_Q_odd h)).symm
    _ = ⨆ U ∈ s13Supp Q ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆, U := by rw [hsupp]
    _ = commSub ⊤ ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ :=
          (commSub_top_eq_iSup_s13Supp h.hW hp3 hp32 h.hQe hZQ).symm

theorem w16n_rk_commSub_top_Q (h : HNon A Q O t) : rk ↥(commSub ⊤ Q) = 6 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have hsupp : s13Supp Q Q = s13IsoComps Q := by
    ext U
    constructor
    · intro hU; exact hU.1
    · intro hU
      refine ⟨hU, ?_⟩
      obtain ⟨U₀, hirr, hne, hUeq⟩ := hU
      intro hbot
      apply hne
      have hle : commSub U₀ Q ≤ commSub U Q :=
        commSub_mono (by rw [hUeq]; exact w16g_le_s13IsoSum_self hirr) le_rfl
      rw [hbot] at hle
      exact le_bot_iff.mp hle
  rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hQe le_rfl, hsupp]
  classical
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype {U : Subgroup W // U ∈ s13IsoComps Q} := Fintype.ofFinite _
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  have hrk : ∀ U ∈ s13IsoComps Q, rk ↥U = 2 := (w16n_shape_aux h).2.2.1
  have hcardN : Nat.card {U : Subgroup W // U ∈ s13IsoComps Q} = 3 := by
    rw [Nat.card_coe_set_eq, (w16n_shape_aux h).2.1]
  have hcong := Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset {U : Subgroup W // U ∈ s13IsoComps Q})) =>
      hrk i.1 i.2)
  rw [hcong, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardN,
    Nat.nsmul_eq_mul]

theorem w16n_commSub_top_eq_conj (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    (hcomm : ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    commSub ⊤ Q = commSub ⊤ (Q.map (MulAut.conj g).toMonoidHom) := by
  have hg' : g⁻¹ ∈ A := A.inv_mem hg
  have hcomm' : ⁅Q, Q.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ := by
    intro hbot
    have hmap := Subgroup.map_commutator (MulAut.conj g).toMonoidHom
      (H₁ := Q) (H₂ := Q.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [hbot, Subgroup.map_bot] at hmap
    rw [w16n_map_conj_inv Q g, Subgroup.commutator_comm] at hmap
    exact hcomm hmap.symm
  have hQZ := w16n_commSub_top_eq_line h hg hcomm
  have hQZ' := w16n_commSub_top_eq_line h hg' hcomm'
  have hZ'map : (⁅Q, Q.map (MulAut.conj g⁻¹).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom = ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ := by
    rw [Subgroup.map_commutator, w16n_map_conj_inv Q g, Subgroup.commutator_comm]
  have hQgZ : commSub ⊤ (Q.map (MulAut.conj g).toMonoidHom) = commSub ⊤ Q := by
    calc commSub ⊤ (Q.map (MulAut.conj g).toMonoidHom)
        = (commSub ⊤ Q).map g.toMonoidHom :=
            CFSG.Quasithin.Asc81c.commSub_map_conj Q g
      _ = (commSub ⊤ ⁅Q, Q.map (MulAut.conj g⁻¹).toMonoidHom⁆).map g.toMonoidHom := by
            rw [hQZ']
      _ = commSub ⊤ ((⁅Q, Q.map (MulAut.conj g⁻¹).toMonoidHom⁆).map
            (MulAut.conj g).toMonoidHom) :=
            (CFSG.Quasithin.Asc81c.commSub_map_conj
              ⁅Q, Q.map (MulAut.conj g⁻¹).toMonoidHom⁆ g).symm
      _ = commSub ⊤ ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ := by rw [hZ'map]
      _ = commSub ⊤ Q := hQZ.symm
  exact hQgZ.symm

end CFSG.LocalAnalysis.WeakClosure81
