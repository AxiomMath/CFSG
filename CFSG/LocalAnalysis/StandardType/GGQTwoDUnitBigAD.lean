module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAA

public section

namespace CFSG.StandardType.QTwo

theorem qtwoDB41_coord_hyperplanes {m : ℕ} (hm : 6 ≤ m) {c : Fin m}
    (I : Finset (Submodule (ZMod 3) (DVec m)))
    (hI : ∀ H ∈ I, Pi.single c 1 ∈ H ∧ Module.finrank (ZMod 3) H = m - 1)
    (hcard : I.card = m - 1)
    (hinf : ∀ v : DVec m, (∀ H ∈ I, v ∈ H) → ∀ i, i ≠ c → v i = 0)
    (hinv : ∀ w ∈ dEvenStab m (Pi.single c 1), ∀ H ∈ I,
      H.map (w : DVec m ≃ₗ[ZMod 3] DVec m).toLinearMap ∈ I) :
    ∀ H ∈ I, ∃ i : Fin m, i ≠ c ∧ ∀ v : DVec m, v ∈ H ↔ v i = 0 := by
  classical
  intro H0 hH0
  obtain ⟨hH0c, hH0fin⟩ := hI H0 hH0
  have hb : Pi.single c 1 = dBasis m c := (Pi.basisFun_apply (ZMod 3) (Fin m) c).symm
  have hH0c' : dBasis m c ∈ H0 := hb ▸ hH0c
  obtain ⟨f, hf0, hfker⟩ := qtwoDB41_dual (by omega : 1 ≤ m) hH0fin
  set B : Finset (Fin m) := qtwoDB41_supp H0 with hBdef
  have hfsupp : ∀ i, i ∈ B ↔ f (dBasis m i) ≠ 0 := by
    intro i
    rw [hBdef, qtwoDB41_mem_supp]
    constructor
    · intro h hf
      exact h (by rw [hfker, LinearMap.mem_ker]; exact hf)
    · intro h hmem
      exact h (by rw [hfker, LinearMap.mem_ker] at hmem; exact hmem)
  have hcB : c ∉ B := by
    rw [hfsupp]
    intro h
    exact h (by simpa [hfker, LinearMap.mem_ker] using hH0c')
  have hBne : B.Nonempty := by
    have := qtwoDB41_supp_nonempty (by omega : 1 ≤ m) hH0fin
    rwa [← hBdef] at this
  have hBsub : B ⊆ Finset.univ.erase c := by
    intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun hic => hcB (hic ▸ hi), Finset.mem_univ i⟩
  have hBs : B.card = 1 := by
    by_contra hne
    have hs2 : 2 ≤ B.card := by
      have := Finset.card_pos.mpr hBne
      omega
    have hsle : B.card ≤ m - 1 := by
      have := qtwoDB41_supp_card_le (c := c) hH0c'
      rwa [← hBdef] at this
    have hKcard : ∀ K : Finset (Fin m), K = (Finset.univ.erase c) \ B →
        K.card = m - 1 - B.card := by
      intro K hK
      rw [hK, Finset.card_sdiff, Finset.card_erase_of_mem (Finset.mem_univ c),
        Finset.card_univ, Fintype.card_fin, Finset.inter_eq_left.mpr hBsub]
    by_cases hsmall : B.card ≤ m - 3
    ·
      let K : Finset (Fin m) := (Finset.univ.erase c) \ B
      let phi : Fin m × Fin m → Submodule (ZMod 3) (DVec m) :=
        fun p => H0.map (dPerm m (Equiv.swap p.1 p.2)).toLinearMap
      have hphi_mem : ∀ p ∈ B.product K, phi p ∈ I := by
        rintro ⟨a,k⟩ hp
        rw [Finset.product_eq_sprod, Finset.mem_product] at hp
        obtain ⟨haB, hkK⟩ := hp
        have hkc : k ≠ c := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hkK).1).1
        have hac : a ≠ c := fun h => hcB (h ▸ haB)
        have hstab : dPerm m (Equiv.swap a k) ∈ dEvenStab m (Pi.single c 1) :=
          qtwoDB41_dPerm_mem_stab (Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hkc))
        exact hinv _ hstab H0 hH0
      have hphi_inj : Set.InjOn phi (↑(B.product K)) := by
        rintro ⟨a,k⟩ hp ⟨a',k'⟩ hp' heq
        change (a, k) ∈ B.product K at hp
        change (a', k') ∈ B.product K at hp'
        rw [Finset.product_eq_sprod, Finset.mem_product] at hp hp'
        obtain ⟨haB, hkK⟩ := hp
        obtain ⟨ha'B, hk'K⟩ := hp'
        have hkNotB : k ∉ B := (Finset.mem_sdiff.mp hkK).2
        have hk'NotB : k' ∉ B := (Finset.mem_sdiff.mp hk'K).2
        have hsupp_eq : qtwoDB41_supp (phi (a,k)) = qtwoDB41_supp (phi (a',k')) := by rw [heq]
        rw [qtwoDB41_supp_map_dPerm_eq, qtwoDB41_supp_map_dPerm_eq,
          qtwoDB41_map_swap_eq haB hkNotB, qtwoDB41_map_swap_eq ha'B hk'NotB] at hsupp_eq
        have hkk' : k = k' := by
          have hmem : k ∈ insert k' (B.erase a') := by
            rw [← hsupp_eq]; exact Finset.mem_insert_self k (B.erase a)
          rcases Finset.mem_insert.mp hmem with h | h
          · exact h
          · exact absurd (Finset.mem_of_mem_erase h) hkNotB
        have hErase : B.erase a = B.erase a' := by
          have h1 : (insert k (B.erase a)).erase k = B.erase a :=
            Finset.erase_insert (fun h => hkNotB (Finset.mem_of_mem_erase h))
          have h2 : (insert k (B.erase a')).erase k = B.erase a' :=
            Finset.erase_insert (fun h => hkNotB (Finset.mem_of_mem_erase h))
          rw [← h1, hsupp_eq, ← hkk', h2]
        have haa' : a = a' := by
          by_contra hne'
          have h1 : a' ∈ B.erase a := Finset.mem_erase.mpr ⟨Ne.symm hne', ha'B⟩
          rw [hErase] at h1
          exact (Finset.notMem_erase a' B) h1
        exact Prod.ext haa' hkk'
      have hbound : (B.product K).card + 1 ≤ I.card := by
        have hsub : insert H0 ((B.product K).image phi) ⊆ I := by
          intro H' hH'
          rcases Finset.mem_insert.mp hH' with rfl | hH'
          · exact hH0
          · rcases Finset.mem_image.mp hH' with ⟨p, hp, rfl⟩
            exact hphi_mem p hp
        have hHnot : H0 ∉ (B.product K).image phi := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨p, hp, hpeq⟩
          rw [Finset.product_eq_sprod, Finset.mem_product] at hp
          obtain ⟨hpB, hkK⟩ := hp
          have hkNotB : p.2 ∉ B := (Finset.mem_sdiff.mp hkK).2
          have hmem2 : p.2 ∈ qtwoDB41_supp (phi p) := by
            rw [qtwoDB41_supp_map_dPerm_eq, qtwoDB41_map_swap_eq hpB hkNotB]
            exact Finset.mem_insert_self _ _
          rw [hpeq, ← hBdef] at hmem2
          exact hkNotB hmem2
        calc (B.product K).card + 1 = (insert H0 ((B.product K).image phi)).card := by
              rw [Finset.card_insert_of_notMem hHnot, Finset.card_image_of_injOn hphi_inj]
          _ ≤ I.card := Finset.card_le_card hsub
      have hTcard : (B.product K).card = B.card * K.card := Finset.card_product B K
      have hbnd : m - 1 < (B.product K).card + 1 := by
        have hKc : K.card = m - 1 - B.card := hKcard K rfl
        rw [hTcard, hKc]
        have hle : m - 1 ≤ B.card * (m - 1 - B.card) := by
          have h1 : 2 * B.card ≤ B.card * (m - 1 - B.card) := by
            calc 2 * B.card = B.card * 2 := by ring
              _ ≤ B.card * (m - 1 - B.card) := Nat.mul_le_mul_left _ (by omega)
          have h2 : 2 * (m - 1 - B.card) ≤ B.card * (m - 1 - B.card) :=
            Nat.mul_le_mul_right _ (by omega)
          have hsum : 2 * (m - 1) = 2 * B.card + 2 * (m - 1 - B.card) := by omega
          omega
        exact Nat.lt_succ_of_le hle
      omega
    · have hge : m - 2 ≤ B.card := by omega
      by_cases heq : B.card = m - 2
      ·
        let K : Finset (Fin m) := (Finset.univ.erase c) \ B
        let phi : Fin m × Fin m → Submodule (ZMod 3) (DVec m) :=
          fun p => H0.map (dPerm m (Equiv.swap p.1 p.2)).toLinearMap
        have hKcard1 : K.card = 1 := by
          rw [hKcard K rfl, heq]; omega
        have hphi_mem : ∀ p ∈ B.product K, phi p ∈ I := by
          rintro ⟨a,k⟩ hp
          rw [Finset.product_eq_sprod, Finset.mem_product] at hp
          obtain ⟨haB, hkK⟩ := hp
          have hkc : k ≠ c := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hkK).1).1
          have hac : a ≠ c := fun h => hcB (h ▸ haB)
          have hstab : dPerm m (Equiv.swap a k) ∈ dEvenStab m (Pi.single c 1) :=
            qtwoDB41_dPerm_mem_stab (Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hkc))
          exact hinv _ hstab H0 hH0
        have hphi_inj : Set.InjOn phi (↑(B.product K)) := by
          rintro ⟨a,k⟩ hp ⟨a',k'⟩ hp' heq'
          change (a, k) ∈ B.product K at hp
          change (a', k') ∈ B.product K at hp'
          rw [Finset.product_eq_sprod, Finset.mem_product] at hp hp'
          obtain ⟨haB, hkK⟩ := hp
          obtain ⟨ha'B, hk'K⟩ := hp'
          have hkNotB : k ∉ B := (Finset.mem_sdiff.mp hkK).2
          have hk'NotB : k' ∉ B := (Finset.mem_sdiff.mp hk'K).2
          have hsupp_eq : qtwoDB41_supp (phi (a,k)) = qtwoDB41_supp (phi (a',k')) := by rw [heq']
          rw [qtwoDB41_supp_map_dPerm_eq, qtwoDB41_supp_map_dPerm_eq,
            qtwoDB41_map_swap_eq haB hkNotB, qtwoDB41_map_swap_eq ha'B hk'NotB] at hsupp_eq
          have hkk' : k = k' := by
            have hmem : k ∈ insert k' (B.erase a') := by
              rw [← hsupp_eq]; exact Finset.mem_insert_self k (B.erase a)
            rcases Finset.mem_insert.mp hmem with h | h
            · exact h
            · exact absurd (Finset.mem_of_mem_erase h) hkNotB
          have hErase : B.erase a = B.erase a' := by
            have h1 : (insert k (B.erase a)).erase k = B.erase a :=
              Finset.erase_insert (fun h => hkNotB (Finset.mem_of_mem_erase h))
            have h2 : (insert k (B.erase a')).erase k = B.erase a' :=
              Finset.erase_insert (fun h => hkNotB (Finset.mem_of_mem_erase h))
            rw [← h1, hsupp_eq, ← hkk', h2]
          have haa' : a = a' := by
            by_contra hne'
            have h1 : a' ∈ B.erase a := Finset.mem_erase.mpr ⟨Ne.symm hne', ha'B⟩
            rw [hErase] at h1
            exact (Finset.notMem_erase a' B) h1
          exact Prod.ext haa' hkk'
        obtain ⟨a, haB, b, hbB, c', hc'B, hab, hac', hbc'⟩ :=
          Finset.two_lt_card.mp (by omega : 2 < B.card)
        have hH1mem : H0.map (dSign m a b).toLinearMap ∈ I := by
          have hstab : dSign m a b ∈ dEvenStab m (Pi.single c 1) :=
            qtwoDB41_dSign_mem_stab hab (fun h => hcB (h ▸ haB)) (fun h => hcB (h ▸ hbB))
          exact hinv _ hstab H0 hH0
        have hH1ne : H0.map (dSign m a b).toLinearMap ≠ H0 :=
          qtwoDB41_map_dSign_ne hfker hab (Ne.symm hac') (Ne.symm hbc') ((hfsupp a).mp haB)
            ((hfsupp b).mp hbB) ((hfsupp c').mp hc'B)
        have hH1supp : qtwoDB41_supp (H0.map (dSign m a b).toLinearMap) = B := by
          rw [qtwoDB41_mem_supp_map_dSign', hBdef]
        have hH0not : H0 ∉ (B.product K).image phi := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨p, hp, hpeq⟩
          rw [Finset.product_eq_sprod, Finset.mem_product] at hp
          obtain ⟨hpB, hkK⟩ := hp
          have hkNotB : p.2 ∉ B := (Finset.mem_sdiff.mp hkK).2
          have hmem2 : p.2 ∈ qtwoDB41_supp (phi p) := by
            rw [qtwoDB41_supp_map_dPerm_eq, qtwoDB41_map_swap_eq hpB hkNotB]
            exact Finset.mem_insert_self _ _
          rw [hpeq, ← hBdef] at hmem2
          exact hkNotB hmem2
        have hH1not : H0.map (dSign m a b).toLinearMap ∉ (B.product K).image phi := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨p, hp, hpeq⟩
          rw [Finset.product_eq_sprod, Finset.mem_product] at hp
          obtain ⟨hpB, hkK⟩ := hp
          have hkNotB : p.2 ∉ B := (Finset.mem_sdiff.mp hkK).2
          have hmem2 : p.2 ∈ qtwoDB41_supp (phi p) := by
            rw [qtwoDB41_supp_map_dPerm_eq, qtwoDB41_map_swap_eq hpB hkNotB]
            exact Finset.mem_insert_self _ _
          rw [hpeq, hH1supp] at hmem2
          exact hkNotB hmem2
        have hbound : (B.product K).card + 2 ≤ I.card := by
          have hsub : insert (H0.map (dSign m a b).toLinearMap)
              (insert H0 ((B.product K).image phi)) ⊆ I := by
            intro H' hH'
            rcases Finset.mem_insert.mp hH' with rfl | hH'
            · exact hH1mem
            rcases Finset.mem_insert.mp hH' with rfl | hH'
            · exact hH0
            · rcases Finset.mem_image.mp hH' with ⟨p, hp, rfl⟩
              exact hphi_mem p hp
          have hnot1 : H0.map (dSign m a b).toLinearMap ∉ insert H0 ((B.product K).image phi) := by
            rw [Finset.mem_insert]
            rintro (h | h)
            · exact hH1ne h
            · exact hH1not h
          calc (B.product K).card + 2 = (insert H0 ((B.product K).image phi)).card + 1 := by
                rw [Finset.card_insert_of_notMem hH0not, Finset.card_image_of_injOn hphi_inj]
            _ = (insert (H0.map (dSign m a b).toLinearMap)
                  (insert H0 ((B.product K).image phi))).card := by
                rw [Finset.card_insert_of_notMem hnot1]
            _ ≤ I.card := Finset.card_le_card hsub
        have hTcard : (B.product K).card = B.card * K.card := Finset.card_product B K
        have hbnd : m - 1 < (B.product K).card + 2 := by
          rw [hTcard, hKcard1, heq]; omega
        omega
      ·
        have heq2 : B.card = m - 1 := by omega
        have hBeq : B = Finset.univ.erase c := by
          apply Finset.eq_of_subset_of_card_le hBsub
          rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
            Fintype.card_fin, heq2]
        obtain ⟨a, haB, b, hbB, d, hdB, hab, had, hbd⟩ :=
          Finset.two_lt_card.mp (by omega : 2 < B.card)
        let F1 : Finset (Submodule (ZMod 3) (DVec m)) :=
          (B.erase a).image (fun x => H0.map (dSign m a x).toLinearMap)
        let H1 : Submodule (ZMod 3) (DVec m) := H0.map (dSign m b d).toLinearMap
        have hF1mem : F1 ⊆ I := by
          intro H' hH'
          rcases Finset.mem_image.mp hH' with ⟨x, hx, rfl⟩
          rw [Finset.mem_erase] at hx
          obtain ⟨hxa, hxB⟩ := hx
          have hstab : dSign m a x ∈ dEvenStab m (Pi.single c 1) :=
            qtwoDB41_dSign_mem_stab (Ne.symm hxa) (fun h => hcB (h ▸ haB))
              (fun h => hcB (h ▸ hxB))
          exact hinv _ hstab H0 hH0
        have hH1mem : H1 ∈ I := by
          have hstab : dSign m b d ∈ dEvenStab m (Pi.single c 1) :=
            qtwoDB41_dSign_mem_stab hbd (fun h => hcB (h ▸ hbB)) (fun h => hcB (h ▸ hdB))
          exact hinv _ hstab H0 hH0
        have hfsuppB : ∀ i, i ∈ B → f (dBasis m i) ≠ 0 := fun i hi => (hfsupp i).mp hi
        have hinj1 : Set.InjOn (fun x => H0.map (dSign m a x).toLinearMap)
            (B.erase a : Set (Fin m)) := by
          intro x hx x' hx' heq'
          rw [Finset.mem_coe, Finset.mem_erase] at hx hx'
          exact qtwoDB41_dSign_family_inj hfker hfsuppB haB hx.2 hx'.2 hx.1 hx'.1 heq'
        have hH0notF1 : H0 ∉ F1 := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨x, hx, heq'⟩
          rw [Finset.mem_erase] at hx
          exact qtwoDB41_dSign_ne_H0 hfker (by omega : 3 ≤ B.card) hfsuppB haB hx.2 hx.1 heq'
        have hH1notF1 : H1 ∉ F1 := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨x, hx, heq'⟩
          rw [Finset.mem_erase] at hx
          obtain ⟨hxa, hxB⟩ := hx
          obtain ⟨y, hyB, hy⟩ :=
            qtwoDB41_exists_out (B := B) (by omega : 4 < B.card) a b d x
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
          obtain ⟨hya, hyb, hyd, hyx⟩ := hy
          have hne_prop : ¬ ∃ mu : ZMod 3,
              f ∘ₗ (dSign m b d).toLinearMap = mu • (f ∘ₗ (dSign m a x).toLinearMap) :=
            qtwoDB41_dSign_ne_dSign hfsuppB haB hyB hab had (Ne.symm hxa)
              hyb hyd hya hyx
          have hker : LinearMap.ker (f ∘ₗ (dSign m b d).toLinearMap) =
              LinearMap.ker (f ∘ₗ (dSign m a x).toLinearMap) := by
            rw [← qtwoDB41_dSign_symm_toLinearMap, ← qtwoDB41_dSign_symm_toLinearMap,
              ← qtwoDB41_map_eq_ker hfker (dSign m b d),
              ← qtwoDB41_map_eq_ker hfker (dSign m a x)]
            exact heq'.symm
          have hg0 : f ∘ₗ (dSign m b d).toLinearMap ≠ 0 := by
            intro h0
            have h1 := congrFun (congrArg DFunLike.coe h0) (dBasis m b)
            simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h1
            rw [qtwoDB41_dSign_apply_self f hbd] at h1
            exact (hfsuppB b hbB) (by simpa using (neg_eq_zero.mp h1))
          have hg0' : f ∘ₗ (dSign m a x).toLinearMap ≠ 0 := by
            intro h0
            have h1 := congrFun (congrArg DFunLike.coe h0) (dBasis m a)
            simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h1
            rw [qtwoDB41_dSign_apply_self f (Ne.symm hxa)] at h1
            exact (hfsuppB a haB) (by simpa using (neg_eq_zero.mp h1))
          exact hne_prop (qtwoDB41_eq_smul_of_ker_eq hker.symm hg0')
        have hH1ne : H1 ≠ H0 := by
          intro heq'
          change H0.map (dSign m b d).toLinearMap = H0 at heq'
          have hker : LinearMap.ker (f ∘ₗ (dSign m b d).toLinearMap) = LinearMap.ker f := by
            rw [← qtwoDB41_dSign_symm_toLinearMap,
              ← qtwoDB41_map_eq_ker hfker (dSign m b d), heq', hfker]
          obtain ⟨mu, hmu⟩ := qtwoDB41_eq_smul_of_ker_eq hker.symm hf0
          have h1 := congrFun (congrArg DFunLike.coe hmu) (dBasis m b)
          simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
            LinearEquiv.coe_toLinearMap] at h1
          rw [qtwoDB41_dSign_apply_self f hbd] at h1
          have hmu_eq : mu = -1 := by
            have h2 : (mu + 1) * f (dBasis m b) = 0 := by
              rw [add_mul, one_mul, ← h1, neg_add_cancel]
            have h3 := (mul_eq_zero.mp h2).resolve_right (hfsuppB b hbB)
            linear_combination h3
          have h2 := congrFun (congrArg DFunLike.coe hmu) (dBasis m a)
          simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
            LinearEquiv.coe_toLinearMap] at h2
          rw [qtwoDB41_dSign_apply_of_ne f hab had, hmu_eq, neg_one_mul] at h2
          have hneg : f (dBasis m a) = -f (dBasis m a) := by simpa using h2
          have hsum : (2 : ZMod 3) * f (dBasis m a) = 0 := by
            rw [two_mul]; exact eq_neg_iff_add_eq_zero.mp hneg
          exact (hfsuppB a haB) ((mul_eq_zero.mp hsum).resolve_left (by decide))
        have hbound : (B.erase a).card + 2 ≤ I.card := by
          have hsub : insert H1 (insert H0 F1) ⊆ I := by
            intro H' hH'
            rcases Finset.mem_insert.mp hH' with rfl | hH'
            · exact hH1mem
            rcases Finset.mem_insert.mp hH' with rfl | hH'
            · exact hH0
            · exact hF1mem hH'
          have hnot1 : H1 ∉ insert H0 F1 := by
            rw [Finset.mem_insert]
            rintro (h | h)
            · exact hH1ne h
            · exact hH1notF1 h
          have hnot0 : H0 ∉ F1 := hH0notF1
          have hcardF1 : F1.card = (B.erase a).card := by
            rw [Finset.card_image_of_injOn hinj1]
          calc (B.erase a).card + 2 = (insert H0 F1).card + 1 := by
                rw [Finset.card_insert_of_notMem hnot0, hcardF1]
            _ = (insert H1 (insert H0 F1)).card := by
                rw [Finset.card_insert_of_notMem hnot1]
            _ ≤ I.card := Finset.card_le_card hsub
        have hcardErase : (B.erase a).card = m - 2 := by
          rw [Finset.card_erase_of_mem haB, heq2]; omega
        omega
  obtain ⟨i, hBi⟩ := Finset.card_eq_one.mp hBs
  refine ⟨i, ?_, ?_⟩
  · rw [hBi] at hcB; exact fun h => hcB (by simpa using h.symm)
  · intro v
    have hfi : f (dBasis m i) ≠ 0 :=
      (hfsupp i).mp (by rw [hBi]; exact Finset.mem_singleton_self i)
    have hfj : ∀ j, j ≠ i → f (dBasis m j) = 0 := by
      intro j hj
      by_contra h
      have : j ∈ B := (hfsupp j).mpr h
      rw [hBi] at this
      exact hj (Finset.mem_singleton.mp this)
    have hfsum : ∀ w : DVec m, f w = ∑ j, (w j) * f (dBasis m j) := by
      intro w
      conv_lhs => rw [← (dBasis m).sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [map_smul, smul_eq_mul, Pi.basisFun_repr]
    constructor
    · intro hv
      have hfv : f v = 0 := (LinearMap.mem_ker).mp (by rw [← hfker]; exact hv)
      rw [hfsum] at hfv
      rw [Finset.sum_eq_single i] at hfv
      · exact (mul_eq_zero.mp hfv).resolve_right hfi
      · intro j _ hj; rw [hfj j hj, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · intro hvi
      have hv0 : f v = 0 := by
        rw [hfsum, Finset.sum_eq_single i]
        · rw [hvi, zero_mul]
        · intro j _ hj; rw [hfj j hj, mul_zero]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hfker, LinearMap.mem_ker]
      exact hv0

end CFSG.StandardType.QTwo

end
