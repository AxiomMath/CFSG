module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenEleven
public import CFSG.Quasithin.Background.Asc81cPfMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

theorem autI_conjSubgroup (hV : IsElemAbelian 2 V) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (X : Subgroup G) :
    autI hV (conjSubgroup X g) =
      (autI hV X).map (MulAut.conj (convI hV ⟨g, hg⟩)⁻¹).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hφ
    have hgy : g * (y : G) * g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg y.2) (Subgroup.inv_mem _ hg)
    refine ⟨convI hV ⟨g * (y : G) * g⁻¹, hgy⟩,
      convI_mem_autI hV (mem_conjSubgroup_iff.1 hy) hgy, ?_⟩
    have e : (⟨g * (y : G) * g⁻¹, hgy⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹ := rfl
    show (MulAut.conj (convI hV ⟨g, hg⟩)⁻¹) (convI hV ⟨g * (y : G) * g⁻¹, hgy⟩) = convI hV y
    rw [MulAut.conj_apply, e, map_mul, map_mul, map_inv]
    group
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hψ
    have hyN : g⁻¹ * (x : G) * g ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) x.2) hg
    refine (mem_autI hV).2 ⟨⟨g⁻¹ * (x : G) * g, hyN⟩, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have : g * (g⁻¹ * (x : G) * g) * g⁻¹ = x := by group
      rw [this]
      exact hx
    · have e : (⟨g⁻¹ * (x : G) * g, hyN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨g, hg⟩⁻¹ * x * ⟨g, hg⟩ := rfl
      show convI hV ⟨g⁻¹ * (x : G) * g, hyN⟩ =
        (MulAut.conj (convI hV ⟨g, hg⟩)⁻¹) (convI hV x)
      rw [MulAut.conj_apply, e, map_mul, map_mul, map_inv]
      group


theorem autI_le_of_forall_mem_mul_centralizer (hV : IsElemAbelian 2 V) {X X' : Subgroup G}
    (hX' : X' ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ x ∈ X', ∃ y ∈ X, x * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    autI hV X' ≤ autI hV X := by
  intro φ hφ
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hφ
  obtain ⟨y, hy, hxy⟩ := h x hx
  have hcN : (x : G) * y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _ hxy
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
    have : y = ((x : G) * y⁻¹)⁻¹ * x := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) x.2
  have h1 : convI hV ⟨(x : G) * y⁻¹, hcN⟩ = 1 := (convI_eq_one_iff hV _).2 hxy
  have e : (⟨(x : G) * y⁻¹, hcN⟩ : Subgroup.normalizer (V : Set G)) = x * ⟨y, hyN⟩⁻¹ := rfl
  rw [e, map_mul, map_inv, mul_inv_eq_one] at h1
  rw [h1]
  exact convI_mem_autI hV hy hyN


theorem autI_commute_of_commutator_eq_bot (hV : IsElemAbelian 2 V) {X X' : Subgroup G}
    (h : ⁅X, X'⁆ = ⊥) : ∀ a ∈ autI hV X, ∀ b ∈ autI hV X', a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 ha
  obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hb
  have hc : ⁅(x : G), (y : G)⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator hx hy
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have hxy : (x : G) * y = y * x := commutatorElement_eq_one_iff_mul_comm.1 hc
  have : x * y = y * x := Subtype.ext hxy
  rw [← map_mul, ← map_mul, this]


theorem eleven_twelve {M V Q U L X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hd : Eleven11Data M V Q U L X)
    {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) : ¬ autI hV X = Y i₀ := by
  intro hX
  obtain ⟨g, hgM, hg⟩ := eleven_five_B hd.setting
    (deltaEleven_subset_gammaEleven M V hd.mem_delta)
  exact hg (eleven_eleven_of_eq hV hd hdec hX hgM)


theorem eleven_thirteen {M V Q U L X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hd : Eleven11Data M V Q U L X)
    (hclose : Eleven11Closing M V Q) {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) (hX : ¬ autI hV X = Y i₀) : False := by
  obtain ⟨h3, hXY, h21, hnc, -⟩ : Nat.card (autI hV X) = 3 ∧ autI hV X ≤ Y i₀ ∧
      Nat.card (Y i₀) = 21 ∧ (∃ a ∈ Y i₀, ∃ b ∈ Y i₀, a * b ≠ b * a) ∧
      ∀ j, Nat.card (Vs j) = 8 := by
    rcases hdec.case with h | h
    · exact absurd h hX
    · exact h
  have hnot := Asc81c.not_le_normalizer_of_frob21 h21 hnc hXY h3
  obtain ⟨φ, hφY, hφN⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨gN, hgM, rfl⟩ := (mem_autI hV).1 (hdec.Y_le i₀ hφY)
  have hgNV : (gN : G) ∈ Subgroup.normalizer (V : Set G) := gN.2
  have hgY : ∀ a ∈ Y i₀, (Y i₀).map (MulAut.conj a).toMonoidHom = Y i₀ := fun a ha =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ha)
  have hgYmap : (Y i₀).map
      (MulAut.conj (convI hV ⟨(gN : G), hd.setting.normal hgM⟩)).toMonoidHom = Y i₀ :=
    hgY _ hφY
  have hU : U ∈ gammaEleven M V := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hW := eleven_eleven_of_frob hV hd hclose hdec hX hgM hgYmap
  have h114 := eleven_four_B hd.setting hU hgM hW hd.mem_blocks hd.mem_blocks
  have hbar : autI hV (conjSubgroup X (gN : G)) =
      (autI hV X).map (MulAut.conj (convI hV gN)⁻¹).toMonoidHom :=
    autI_conjSubgroup hV hgNV X
  have hne : (autI hV X).map (MulAut.conj (convI hV gN)⁻¹).toMonoidHom ≠ autI hV X := by
    intro h
    apply hφN
    have h1 : (convI hV gN)⁻¹ ∈ Subgroup.normalizer (autI hV X : Set _) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 h
    simpa using inv_mem h1
  have hne' : autI hV X ≠ autI hV (conjSubgroup X (gN : G)) := fun h =>
    hne (hbar.symm.trans h.symm)
  have hbar3 : Nat.card (autI hV (conjSubgroup X (gN : G))) = 3 := by
    rw [hbar, Subgroup.card_map_of_injective (MulEquiv.injective _), h3]
  have hbarY : autI hV (conjSubgroup X (gN : G)) ≤ Y i₀ := by
    rw [hbar]
    calc (autI hV X).map (MulAut.conj (convI hV gN)⁻¹).toMonoidHom
        ≤ (Y i₀).map (MulAut.conj (convI hV gN)⁻¹).toMonoidHom := Subgroup.map_mono hXY
      _ = Y i₀ := hgY _ ((Y i₀).inv_mem hφY)
  have hXL : X ≤ L := hd.isHall.1.trans inf_le_left
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  rcases h114 with hcomm | hLL
  · have hcX : ⁅X, conjSubgroup X (gN : G)⁆ = ⊥ :=
      le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hXL (conjSubgroup_mono_left _ hXL))
    have hc := autI_commute_of_commutator_eq_bot hV hcX
    have hsup := Asc81c.sup_eq_of_frob21 h21 hXY hbarY h3 hbar3 hne'
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    apply hab
    rw [← hsup] at ha hb
    have hXc := Asc81c.comm_of_card_prime Nat.prime_three h3
    have hXc' := Asc81c.comm_of_card_prime Nat.prime_three hbar3
    have hc1 : ∀ a ∈ autI hV X ⊔ autI hV (conjSubgroup X (gN : G)), ∀ x ∈ autI hV X,
        x * a = a * x := by
      intro a ha
      have : autI hV X ⊔ autI hV (conjSubgroup X (gN : G)) ≤
          Subgroup.centralizer (autI hV X : Set _) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => hXc x hx a ha)
          (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => hc x hx a ha)
      exact fun x hx => Subgroup.mem_centralizer_iff.1 (this ha) x hx
    have hc2 : ∀ a ∈ autI hV X ⊔ autI hV (conjSubgroup X (gN : G)),
        ∀ x ∈ autI hV (conjSubgroup X (gN : G)), x * a = a * x := by
      intro a ha
      have : autI hV X ⊔ autI hV (conjSubgroup X (gN : G)) ≤
          Subgroup.centralizer (autI hV (conjSubgroup X (gN : G)) : Set _) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => (hc a ha x hx).symm)
          (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => hXc' x hx a ha)
      exact fun x hx => Subgroup.mem_centralizer_iff.1 (this ha) x hx
    have hfin : autI hV X ⊔ autI hV (conjSubgroup X (gN : G)) ≤
        Subgroup.centralizer ({b} : Set (MulAut (IntMod V hV))) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact (hc1 b hb x hx).symm)
        (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact (hc2 b hb x hx).symm)
    exact (Subgroup.mem_centralizer_iff.1 (hfin ha) b rfl).symm
  · have hMg : conjSubgroup M (gN : G) = M :=
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hgM)
    have hLM : conjSubgroup (L ⊓ M) (gN : G) = L ⊓ M := by
      rw [conjSubgroup_inf, ← hLL, hMg]
    have hHall' : IsHallTwoPrimeOf (conjSubgroup X (gN : G)) (L ⊓ M) := by
      have := isHallTwoPrimeOf_conjSubgroup hd.isHall (gN : G)
      rwa [hLM] at this
    have hX'N : conjSubgroup X (gN : G) ≤ Subgroup.normalizer (V : Set G) := by
      have : conjSubgroup X (gN : G) ≤ conjSubgroup M (gN : G) :=
        conjSubgroup_mono_left _ hXM
      rw [hMg] at this
      exact this.trans hd.setting.normal
    have hmod := eleven_ten_hall_mod hd hHall' hd.isHall
    have hle := autI_le_of_forall_mem_mul_centralizer hV hX'N hmod
    have heq : autI hV (conjSubgroup X (gN : G)) = autI hV X :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hbar3, h3])
    exact hne (hbar.symm.trans heq)


theorem eleven_one_of_closing
    {M V Q : Subgroup G} (hset : Setting11 M V Q)
    (hclose : Eleven11Closing M V Q) (h2 : 2 < mBar M ⊥ V hset.isElemAbelian) :
    (mBar M ⊥ V hset.isElemAbelian : ℕ∞) ≤ rMV M V := by
  by_contra hlt
  have hlt' : rMV M V < (mBar M ⊥ V hset.isElemAbelian : ℕ∞) := not_le.1 hlt
  obtain ⟨U, L, X, hd⟩ := exists_eleven11Data hset h2 hlt'
  obtain ⟨s, Y, Vs, i₀, hdec⟩ :=
    exists_eleven11Decomp Asc81c.Pf.thm104 hset.isElemAbelian hd
  exact eleven_thirteen hset.isElemAbelian hd hclose hdec
    (eleven_twelve hset.isElemAbelian hd hdec)

theorem w3Thm111_of_closing
    (hclose : ∀ M V Q : Subgroup G, Setting11 M V Q → Eleven11Closing M V Q) :
    ∀ M V Q : Subgroup G, Setting11 M V Q → MBarGT M ⊥ V 2 →
      ∀ n : ℕ, MBarGT M ⊥ V n → (n : ℕ∞) < rMV M V := by
  intro M V Q hset h2 n hn
  have hV := hset.isElemAbelian
  have hbot : M ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have h2' : 2 < mBar M ⊥ V hV :=
    (mBarGT_iff_lt_mBar M ⊥ V hV bot_le hset.normal hbot 2).1 h2
  have hn' : n < mBar M ⊥ V hV :=
    (mBarGT_iff_lt_mBar M ⊥ V hV bot_le hset.normal hbot n).1 hn
  have := eleven_one_of_closing hset (hclose M V Q hset) h2'
  exact lt_of_lt_of_le (by exact_mod_cast hn') this

end CFSG.LocalAnalysis.WeakClosure81
